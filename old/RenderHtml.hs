-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RenderHtml (renderResults, renderResultsInc, renderStandaloneHTML) where

import Text.Blaze.Internal (MarkupM)
import Text.Blaze.Html5 as H hiding (map, a, b)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.ByteString.Lazy (toStrict)
import qualified Data.ByteString as BS
import Data.Aeson (ToJSON (..), encode)
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Data.Foldable (fold)
import Data.Maybe (fromJust)
import Data.Functor ((<&>))
import Data.String (fromString)
import Data.Text    qualified as T
import CMark (commonmarkToHtml)
import GHC.Generics

import Err
import PPrint
import Types.Source
import Util (unsnoc, foldMapM)
import IncState
import Live.Eval

type RenderingState  = NodeList       RenderedCellState
type RenderingUpdate = NodeListUpdate RenderedCellState

data RenderedCellState = RenderedCellState RenderedSourceBlock CellStatus RenderedOutputs
     deriving Generic

data RenderedCellUpdate = RenderedCellUpdate (Overwrite CellStatus) RenderedOutputs
     deriving Generic

instance Semigroup RenderedCellUpdate where
  RenderedCellUpdate s o <> RenderedCellUpdate s' o' = RenderedCellUpdate (s<>s') (o<>o')

instance Monoid RenderedCellUpdate where
  mempty = RenderedCellUpdate mempty mempty

instance ToJSON RenderedCellState
instance ToJSON RenderedCellUpdate

instance IncState RenderedCellState where
  type Delta RenderedCellState = RenderedCellUpdate
  applyDiff (RenderedCellState sb status result) (RenderedCellUpdate status' result') =
    RenderedCellState sb (fromOverwritable (applyDiff (Overwritable status) status')) (result <> result')

renderResults :: CellsState -> IO RenderingUpdate
renderResults cellsState = fst <$> renderResultsInc cellsState

renderResultsInc :: CellsState -> IO (RenderingUpdate, CellsUpdate -> IO RenderingUpdate)
renderResultsInc initState = do
  (initRender, updates) <- runIncM renderCells initState
  return (nodeListAsUpdate initRender, updates)

type BlockId = Int

renderCells :: IncVar CellsState -> IncM (IncVar RenderingState)
renderCells cells = fmapNodeList cells renderCell

renderCell :: BlockId -> IncVar CellState -> IncM (IncVar RenderedCellState)
renderCell blockId cellState = do
  (sourceBlock, status, outputs) <- unpackCellStateInc cellState
  sourceBlock' <- fmapAllOrNothing sourceBlock $ renderSourceBlock blockId
  outputs' <- renderOutputs outputs
  packRenderedCellState sourceBlock' status outputs'

renderOutputs :: IncVar (MonoidState Outputs) -> IncM (IncVar (MonoidState RenderedOutputs))
renderOutputs outputsVar = liftMonoidStateIncM outputsVar do
  return \(Outputs outs) -> foldMapM renderOutput outs

fmapNodeList :: IncVar (NodeList a) -> (BlockId -> IncVar a -> IncM (IncVar b)) -> IncM (IncVar (NodeList b))
fmapNodeList nl f = do
  (l, m) <- unpackNodeList nl
  m' <- fmapIncMap m f
  packNodeList l m'

unpackCellStateInc
  :: IncVar CellState -> IncM ( IncVar (Unchanging SourceBlock)
                              , IncVar (Overwritable CellStatus)
                              , IncVar (MonoidState Outputs) )
unpackCellStateInc cellState = do
  incUnzip3 =<< fmapIncVar cellState
    (\(CellState sb s outs) -> (Unchanging sb, Overwritable s, MonoidState outs))
    (\(CellUpdate s outs) -> ((), s, outs))

packRenderedCellState
  :: IncVar (Unchanging RenderedSourceBlock)
  -> IncVar (Overwritable CellStatus)
  -> IncVar (MonoidState RenderedOutputs)
  -> IncM (IncVar RenderedCellState)
packRenderedCellState sourceBlock status outputs = do
  renderedCellState <- incZip3 sourceBlock status outputs
  fmapIncVar renderedCellState
    (\(Unchanging sb, Overwritable s, MonoidState outs) -> RenderedCellState sb s outs)
    (\((), s, outs) -> RenderedCellUpdate s outs)

unpackNodeList :: IncVar (NodeList a) -> IncM (IncVar [NodeId], IncVar (M.Map NodeId a))
unpackNodeList nl = do
  incUnzip2 =<< fmapIncVar nl (\(NodeList l m) -> (l, m)) (\(NodeListUpdate l m) -> (l, m))

packNodeList :: IncVar [NodeId] -> IncVar (M.Map NodeId a) -> IncM (IncVar (NodeList a))
packNodeList lv mv = do
  nl <- incZip2 lv mv
  fmapIncVar nl (\(l, m) -> NodeList l m) (\(l, m) -> NodeListUpdate l m)

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
  | RenderedTreeNodeUpdate [(SrcId, MapEltUpdate TreeNodeState)]
  | RenderedFocusUpdate [(LexemeId, SrcId)]
    deriving (Generic)

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

instance Semigroup TreeNodeUpdate where
  TreeNodeUpdate x y <> TreeNodeUpdate x' y' = TreeNodeUpdate (x<>x') (y<>y')

instance Monoid TreeNodeUpdate where
  mempty = TreeNodeUpdate mempty mempty

instance IncState TreeNodeState where
  type Delta TreeNodeState = TreeNodeUpdate
  applyDiff (TreeNodeState s h t) (TreeNodeUpdate h' t') =
    TreeNodeState s (h<>h') (t<>fold t')

renderOutput :: Output -> IO [RenderedOutput]
renderOutput = \case
  TextOut s      -> emit $ RenderedTextOut s
  HtmlOut s      -> emit $ RenderedHtmlOut s
  SourceInfo s   -> case s of
    SIGroupingInfo  info -> return $ renderGroupingInfo  info
    SINamingInfo    info -> return $ renderNamingInfo    info
    SITypingInfo    info -> return $ renderTypingInfo    info
  PassResult n s -> emit $ RenderedPassResult n s
  MiscLog s      -> emit $ RenderedMiscLog s
  Error e        -> emit $ RenderedError (getErrSrcId e) (pprint e)
  where emit :: RenderedOutput -> IO [RenderedOutput]
        emit x = return [x]

renderSourceBlock :: BlockId -> SourceBlock -> RenderedSourceBlock
renderSourceBlock n b = RenderedSourceBlock
  { rsbLine       = sbLine b
  , rsbNumLines   = length $ lines $ T.unpack $ sbText b
  , rsbBlockId    = n
  , rsbLexemeList = unsnoc $ lexemeList $ sbLexemeInfo b
  , rsbText = T.unpack $ sbText b
  , rsbHtml = renderHtml case sbContents b of
      Misc (ProseBlock s) -> cdiv "prose-block" $ mdToHtml s
      UnParseable _ e -> do
        cdiv "code-block" (toHtml $ sbText b)
        cdiv "err-result" (toHtml e)
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
  where treeNodeUpdate = fold $ M.toList m <&> \(sid, node) -> renderNameInfo sid node

renderNameInfo :: SrcId -> NameInfo -> [(SrcId, MapEltUpdate TreeNodeState)]
renderNameInfo sid = \case
  LocalOcc binderSid -> do
    let occUpdate = (sid, Update $ TreeNodeUpdate [(binderSid, HighlightBinder)] ["Local name"])
    let binderUpdate = (binderSid, Update $ TreeNodeUpdate [(sid, HighlightOcc)] [])
    [occUpdate, binderUpdate]
  -- TODO: this path isn't exercised because we don't actually generate any
  -- `LocalBinder` info in `SourceRename`
  LocalBinder binderScope -> [(sid, Update $ TreeNodeUpdate (selfHighlight:scopeHighlights) mempty)]
    where selfHighlight = (sid, HighlightBinder)
          scopeHighlights = binderScope <&> \scopeSid -> (scopeSid, HighlightScope)
  TopOcc s -> [(sid, Update $ TreeNodeUpdate [] [s])]

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

renderStandaloneHTML :: FilePath -> RenderingUpdate -> IO ()
renderStandaloneHTML pagePath renderingInfo = do
  let jsonPath = pagePath ++ ".json"
  let htmlPath = pagePath ++ ".html"
  BS.writeFile jsonPath $ toStrict $ encode renderingInfo
  writeFile htmlPath $ renderHtml $ buildMainHtml jsonPath

buildMainHtml :: FilePath -> Html
buildMainHtml jsonPath = docTypeHtml $ do
  H.head do
    H.meta ! charset "UTF-8"
    H.link ! rel "stylesheet" ! type_ "text/css" ! href "/dex-lang/static/style.css"
  H.body ! onload (textValue $ fromString jsSource) $ do
    H.div mempty ! At.id "minimap"
    H.div "(hover over code for more information)" ! At.id "hover-info"
    H.div mempty ! At.id "main-output"
    H.script ! src "/dex-lang/static/index.js" $ mempty
  where
    jsSource :: String
    jsSource = "render('Static', '/" ++ jsonPath ++ "');"

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
