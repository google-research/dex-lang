-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RenderHtml (
  progHtml, pprintHtml, ToMarkup, renderSourceBlock,
  RenderedSourceBlock, RenderedOutputs, SourceBlockWithId (..)) where

import Text.Blaze.Internal (MarkupM)
import Text.Blaze.Html5 as H hiding (map, b)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.Aeson (ToJSON (..))
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Data.Foldable (fold)
import Data.Maybe (fromJust)
import Data.Functor ((<&>))
import Data.String (fromString)
import Data.Text    qualified as T
import Data.Text.IO qualified as T
import CMark (commonmarkToHtml)
import System.IO.Unsafe
import GHC.Generics

import Err
import Paths_dex (getDataFileName)
import PPrint
import Types.Source
import Util (unsnoc)
import IncState

-- === rendering source blocks and results ===

type BlockId = Int
data SourceBlockWithId = SourceBlockWithId
  { sourceBlockId        :: BlockId
  , sourceBlockWithoutId :: SourceBlock }
  deriving (Show, Generic)

instance ToJSON SourceBlockWithId where
  toJSON (SourceBlockWithId n b) = toJSON $ renderSourceBlock n b

instance ToJSON Outputs where
  toJSON x = toJSON $ renderOutputs x

-- === rendering results ===

-- RenderedOutputs, RenderedSourceBlock aren't 100% HTML themselves but the idea
-- is that they should be trivially convertable to JSON and sent over to the
-- client which can do the final rendering without much code or runtime work.

data RenderedSourceBlock = RenderedSourceBlock
  { rsbLine       :: Int
  , rsbNumLines   :: Int
  , rsbBlockId    :: BlockId
  , rsbLexemeList :: [SrcId]
  , rsbText       :: String
  , rsbHtml       :: String}
  deriving (Generic)

type RenderedOutputs = [RenderedOutput]
data RenderedOutput =
    RenderedTextOut String
  | RenderedHtmlOut String
  | RenderedPassResult PassName (Maybe String)
  | RenderedMiscLog String
  | RenderedError (Maybe SrcId) String
  | RenderedTreeNodeUpdate [(SrcId, MapEltUpdate TreeNodeState TreeNodeUpdate)]
  | RenderedFocusUpdate [(LexemeId, SrcId)]
    deriving (Show, Eq, Generic)

data HighlightType =
   HighlightGroup
 | HighlightLeaf
 | HighlightError
 | HighlightBinder
 | HighlightOcc
 | HighlightScope
   deriving (Show, Eq, Generic)

type RenderedHighlight = (SrcId, HighlightType)
data TreeNodeState  = TreeNodeState
  { tnSpan       :: (LexemeId, LexemeId)
  , tnHighlights :: [RenderedHighlight]
  , tnText       :: String }
  deriving (Show, Eq, Generic)

data TreeNodeUpdate = TreeNodeUpdate
  { tnuHighlights :: [RenderedHighlight]
  , tnuText       :: [String] }
    deriving (Show, Eq, Generic)

renderOutputs :: Outputs -> RenderedOutputs
renderOutputs (Outputs outs) = foldMap renderOutput outs

renderOutput :: Output -> [RenderedOutput]
renderOutput = \case
  TextOut s      -> pure $ RenderedTextOut s
  HtmlOut s      -> pure $ RenderedHtmlOut s
  SourceInfo s   -> case s of
    SIGroupingInfo  info -> renderGroupingInfo  info
    SINamingInfo    info -> renderNamingInfo    info
    SITypingInfo    info -> renderTypingInfo      info
  PassResult n s -> pure $ RenderedPassResult n s
  MiscLog s      -> pure $ RenderedMiscLog s
  Error e        -> pure $ RenderedError (getErrSrcId e) (pprint e)

renderSourceBlock :: BlockId -> SourceBlock -> RenderedSourceBlock
renderSourceBlock n b = RenderedSourceBlock
  { rsbLine       = sbLine b
  , rsbNumLines   = length $ lines $ T.unpack $ sbText b
  , rsbBlockId    = n
  , rsbLexemeList = unsnoc $ lexemeList $ sbLexemeInfo b
  , rsbText = T.unpack $ sbText b
  , rsbHtml = renderHtml case sbContents b of
      Misc (ProseBlock s) -> cdiv "prose-block" $ mdToHtml s
      _ -> renderSpans n (sbLexemeInfo b) (sbText b)
  }

renderGroupingInfo :: GroupingInfo -> RenderedOutputs
renderGroupingInfo (GroupingInfo m) =
  [ RenderedFocusUpdate    focus
  , RenderedTreeNodeUpdate treeNodeUpdate]
  where
    treeNodeUpdate = M.toList m <&> \(sid, node) -> (sid, Create $ renderTreeNode m sid node)
    focus = fold $ uncurry renderFocus <$> M.toList m

renderTreeNode :: M.Map SrcId GroupTreeNode -> SrcId -> GroupTreeNode -> TreeNodeState
renderTreeNode m sid node = TreeNodeState (gtnSpan node) (getHighlights m sid node) ""

getHighlights :: M.Map SrcId GroupTreeNode -> SrcId -> GroupTreeNode -> [RenderedHighlight]
getHighlights m sid node = case gtnChildren node of
  [] -> [(sid, HighlightGroup)]
  children -> children <&> \childSrcId -> do
    let child = fromJust $ M.lookup childSrcId m
    let highlight = case gtnIsAtomicLexeme child of
                      True  -> HighlightLeaf
                      False -> HighlightGroup
    (childSrcId, highlight)

renderFocus :: SrcId -> GroupTreeNode -> [(LexemeId, SrcId)]
renderFocus srcId node = case gtnChildren node of
  [] -> case gtnIsAtomicLexeme node of
    False -> [(srcId, srcId)]
    True -> case gtnParent node of
      Nothing -> [(srcId, srcId)]
      Just parentId -> [(srcId, parentId)]
  _ -> []  -- not a lexeme

renderNamingInfo :: NamingInfo -> RenderedOutputs
renderNamingInfo (NamingInfo m) = [RenderedTreeNodeUpdate treeNodeUpdate]
  where
    treeNodeUpdate = M.toList m <&> \(sid, node) ->
      (sid, Update $ renderNameInfo node)

renderNameInfo :: NameInfo -> TreeNodeUpdate
renderNameInfo = \case
  LocalOcc _ -> TreeNodeUpdate [] ["Local name"]
  LocalBinder _ -> TreeNodeUpdate mempty mempty
  TopOcc s -> TreeNodeUpdate [] [s]

renderTypingInfo :: TypingInfo -> RenderedOutputs
renderTypingInfo (TypingInfo m) = [RenderedTreeNodeUpdate treeNodeUpdate]
  where
    treeNodeUpdate = M.toList m <&> \(sid, node) ->
      (sid, Update $ renderTypeInfo node)

renderTypeInfo :: TypeInfo -> TreeNodeUpdate
renderTypeInfo = \case
  ExprType s -> TreeNodeUpdate mempty ["Type:   " <> s]
  _ -> TreeNodeUpdate mempty mempty

instance ToJSON RenderedSourceBlock
instance ToJSON RenderedOutput
instance ToJSON TreeNodeState
instance ToJSON TreeNodeUpdate
instance ToJSON HighlightType

-- -----------------

cssSource :: T.Text
cssSource = unsafePerformIO $
  T.readFile =<< getDataFileName "static/style.css"
{-# NOINLINE cssSource #-}

javascriptSource :: T.Text
javascriptSource = unsafePerformIO $
  T.readFile =<< getDataFileName "static/index.js"
{-# NOINLINE javascriptSource #-}

pprintHtml :: ToMarkup a => a -> String
pprintHtml x = renderHtml $ toMarkup x

progHtml :: (ToMarkup a, ToMarkup b) => [(a, b)] -> String
progHtml blocks = renderHtml $ wrapBody $ map toHtmlBlock blocks
  where toHtmlBlock (block,outputs) = toMarkup block <> toMarkup outputs

wrapBody :: [Html] -> Html
wrapBody blocks = docTypeHtml $ do
  H.head $ do
    H.meta ! charset "UTF-8"
    -- Base CSS stylesheet.
    H.style ! type_ "text/css" $ toHtml cssSource
    -- KaTeX CSS and JavaScript.
    H.link ! rel "stylesheet" ! href "https://cdn.jsdelivr.net/npm/katex@0.12.0/dist/katex.min.css"
    H.script ! defer "" ! src "https://cdn.jsdelivr.net/npm/katex@0.12.0/dist/katex.min.js" $ mempty
    H.script ! defer "" ! src "https://cdn.jsdelivr.net/npm/katex@0.12.0/dist/contrib/auto-render.min.js"
             ! onload jsSource $ mempty
  H.body $ H.div inner ! At.id "main-output"
  where
    inner = foldMap (cdiv "cell") blocks
    jsSource = textValue $ javascriptSource <> "render(RENDER_MODE.STATIC);"

mdToHtml :: T.Text -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] s

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

renderSpans :: BlockId -> LexemeInfo -> T.Text -> Markup
renderSpans blockId lexInfo sourceText = cdiv "code-block" do
  runTextWalkerT sourceText do
    forM_ (lexemeList lexInfo) \sourceId -> do
      let (lexemeTy, (l, r)) = fromJust $ M.lookup sourceId (lexemeInfo lexInfo)
      takeTo l >>= emitWhitespace
      takeTo r >>= emitSpan (Just (blockId, sourceId)) (lexemeClass lexemeTy)
    takeRest >>= emitSpan Nothing (Just "comment")

emitWhitespace :: T.Text -> TextWalker ()
emitWhitespace t
  | t == ""     = return ()
  | blankText t = emitSpan Nothing Nothing t
  | otherwise   = emitSpan Nothing (Just "comment") t

blankText :: T.Text -> Bool
blankText t = all (==' ') $ T.unpack t

emitSpan :: Maybe (BlockId, SrcId) -> Maybe String -> T.Text -> TextWalker ()
emitSpan maybeSrcId className t = lift do
  let classAttr = case className of
        Nothing -> mempty
        Just c -> class_ (stringValue c)
  let idAttr = case maybeSrcId of
        Nothing -> mempty
        Just (bid, SrcId sid) -> At.id (fromString $ "span_" ++ show bid ++ "_"++ show sid)
  H.span (toHtml t) ! classAttr ! idAttr

lexemeClass :: LexemeType -> Maybe String
lexemeClass = \case
   Keyword             -> Just "keyword"
   Symbol              -> Just "symbol"
   TypeName            -> Just "type-name"
   LowerName           -> Nothing
   UpperName           -> Nothing
   LiteralLexeme       -> Just "literal"
   StringLiteralLexeme -> Nothing
   MiscLexeme          -> Nothing

type TextWalker a = StateT (Int, T.Text) MarkupM a

runTextWalkerT :: T.Text -> TextWalker a -> MarkupM a
runTextWalkerT t cont = evalStateT cont (0, t)

-- index is the *absolute* index, from the very beginning
takeTo :: Int -> TextWalker T.Text
takeTo startPos = do
  (curPos, curText) <- get
  let (prefix, remText) = T.splitAt (startPos- curPos) curText
  put (startPos, remText)
  return prefix

takeRest :: TextWalker T.Text
takeRest = do
  (curPos, curText) <- get
  put (curPos + T.length curText, mempty)
  return curText
