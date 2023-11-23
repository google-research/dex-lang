-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RenderHtml (pprintHtml, progHtml, ToMarkup) where

import Text.Blaze.Internal (MarkupM)
import Text.Blaze.Html5 as H hiding (map)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import qualified Data.Map.Strict as M
import Control.Monad.State.Strict
import Data.Maybe (fromJust)
import Data.Text    qualified as T
import Data.Text.IO qualified as T
import CMark (commonmarkToHtml)
import System.IO.Unsafe


import Err
import Paths_dex (getDataFileName)
import PPrint ()
import Types.Misc
import Types.Source

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

instance ToMarkup Result where
  toMarkup (Result outs err) = foldMap toMarkup outs <> err'
    where err' = case err of
                   Failure e  -> cdiv "err-block" $ toHtml $ pprint e
                   Success () -> mempty

instance ToMarkup Output where
  toMarkup out = case out of
    HtmlOut s -> preEscapedString s
    _ -> cdiv "result-block" $ toHtml $ pprint out

instance ToMarkup SourceBlock where
  toMarkup block = case sbContents block of
    (Misc (ProseBlock s)) -> cdiv "prose-block" $ mdToHtml s
    _ -> renderSpans (sbLexemeInfo block) (sbASTInfo block) (sbText block)

mdToHtml :: T.Text -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] s

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

renderSpans :: LexemeInfo -> ASTInfo -> T.Text -> Markup
renderSpans lexInfo astInfo sourceText = cdiv "code-block" do
  runTextWalkerT sourceText do
    forM_ (lexemeList lexInfo) \sourceId -> do
      let (lexemeTy, (l, r)) = fromJust $ M.lookup sourceId (lexemeInfo lexInfo)
      takeTo l >>= emitSpan ""
      takeTo r >>= emitSpan (lexemeClass lexemeTy)
    takeRest >>= emitSpan ""

emitSpan :: String -> T.Text -> TextWalker ()
emitSpan className t = lift $ H.span (toHtml t) ! class_ (stringValue className)

lexemeClass :: LexemeType -> String
lexemeClass = \case
   Keyword             -> "keyword"
   Symbol              -> "symbol"
   TypeName            -> "type-name"
   LowerName           -> ""
   UpperName           -> ""
   LiteralLexeme       -> "literal"
   StringLiteralLexeme -> ""
   MiscLexeme          -> ""

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
  endPos <- gets $ T.length . snd
  takeTo endPos
