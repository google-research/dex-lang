-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RenderHtml (
  progHtml, ToMarkup, renderSourceBlock, renderResult,
  RenderedSourceBlock, RenderedResult) where

import Text.Blaze.Internal (MarkupM)
import Text.Blaze.Html5 as H hiding (map, b)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.Aeson (ToJSON)
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Functor ((<&>))
import Data.Maybe (fromJust)
import Data.String (fromString)
import Data.Text    qualified as T
import Data.Text.IO qualified as T
import CMark (commonmarkToHtml)
import System.IO.Unsafe
import GHC.Generics

import Err
import Paths_dex (getDataFileName)
import PPrint ()
import Types.Source
import Util (unsnoc, foldJusts)

-- === rendering results ===

-- RenderedResult, RenderedSourceBlock aren't 100% HTML themselves but the idea
-- is that they should be trivially convertable to JSON and sent over to the
-- client which can do the final rendering without much code or runtime work.

type BlockId = Int
data RenderedSourceBlock = RenderedSourceBlock
  { rsbLine      :: Int
  , rsbBlockId   :: BlockId
  , rsbLexemeList :: [SrcId]
  , rsbHtml       :: String }
  deriving (Generic)

data RenderedResult = RenderedResult
  { rrHtml         :: String
  , rrHighlightMap :: HighlightMap
  , rrHoverInfoMap :: HoverInfoMap }
  deriving (Generic)

renderResult :: Result -> RenderedResult
renderResult r = RenderedResult
  { rrHtml         = pprintHtml r
  , rrHighlightMap = computeHighlights r
  , rrHoverInfoMap = computeHoverInfo r }

renderSourceBlock :: BlockId -> SourceBlock -> RenderedSourceBlock
renderSourceBlock n b = RenderedSourceBlock
  { rsbLine    = sbLine b
  , rsbBlockId = n
  , rsbLexemeList = unsnoc $ lexemeList $ sbLexemeInfo b
  , rsbHtml = renderHtml case sbContents b of
      Misc (ProseBlock s) -> cdiv "prose-block" $ mdToHtml s
      _ -> renderSpans n (sbLexemeInfo b) (sbText b)
  }

instance ToMarkup Result where
  toMarkup (Result outs err) = foldMap toMarkup outs <> err'
    where err' = case err of
                   Failure e  -> cdiv "err-block" $ toHtml $ pprint e
                   Success () -> mempty

instance ToMarkup Output where
  toMarkup out = case out of
    HtmlOut s -> preEscapedString s
    SourceInfo _ -> mempty
    _ -> cdiv "result-block" $ toHtml $ pprint out

instance ToJSON RenderedResult
instance ToJSON RenderedSourceBlock

-- === textual information on hover ===

type HoverInfo = String
newtype HoverInfoMap = HoverInfoMap (M.Map LexemeId HoverInfo)   deriving (ToJSON, Semigroup, Monoid)

computeHoverInfo :: Result -> HoverInfoMap
computeHoverInfo _ = mempty

-- === highlighting on hover ===

newtype FocusMap = FocusMap (M.Map LexemeId SrcId)   deriving (ToJSON, Semigroup, Monoid)
newtype HighlightMap = HighlightMap (M.Map SrcId Highlights)  deriving (ToJSON, Semigroup, Monoid)
type Highlights = [(HighlightType, LexemeSpan)]
data HighlightType = HighlightGroup | HighlightLeaf  deriving Generic

instance ToJSON HighlightType

computeHighlights :: Result -> HighlightMap
computeHighlights result = do
  execWriter $ mapM go $ foldJusts (resultOutputs result) \case
    SourceInfo (SIGroupTree t) -> Just t
    _ -> Nothing
 where
  go :: GroupTree -> Writer HighlightMap ()
  go t = do
    let children = gtChildren t
    let highlights = children <&> \child ->
          (getHighlightType (gtIsAtomicLexeme child), gtSpan child)
    forM_ children \child-> do
      tell $ HighlightMap $ M.singleton (gtSrcId child) highlights
      go child

  getHighlightType :: Bool -> HighlightType
  getHighlightType True  = HighlightLeaf
  getHighlightType False = HighlightGroup

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
  where toHtmlBlock (block,result) = toMarkup block <> toMarkup result

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
      takeTo l >>= emitSpan Nothing (Just "comment")
      takeTo r >>= emitSpan (Just (blockId, sourceId)) (lexemeClass lexemeTy)
    takeRest >>= emitSpan Nothing (Just "comment")

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
