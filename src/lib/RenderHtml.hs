-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module RenderHtml (pprintHtml, progHtml, ToMarkup, treeToHtml) where

import Text.Blaze.Html5 as H hiding (map)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.List    qualified as L
import Data.Text    qualified as T
import Data.Text.IO qualified as T
import CMark (commonmarkToHtml)
import System.IO.Unsafe

import Control.Monad
import Text.Megaparsec hiding (chunk)
import Text.Megaparsec.Char as C

import Err
import Lexing (Parser, symChar, keyWordStrs, symbol, parseit, withSource)
import Paths_dex (getDataFileName)
import PPrint ()
import SourceInfo
import TraverseSourceInfo
import Types.Misc
import Types.Source
import Util

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
    TopDecl decl -> renderSpans decl block
    Command _ g -> renderSpans g block
    _ -> cdiv "code-block" $ highlightSyntax (sbText block)

mdToHtml :: T.Text -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] s

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

-- === syntax highlighting ===

spanDelimitedCode :: SourceBlock -> [SrcPosCtx] -> Html
spanDelimitedCode block ctxs =
  let (Just tree) = srcCtxsToTree block ctxs in
  spanDelimitedCode' block tree

spanDelimitedCode' :: SourceBlock -> SpanTree -> Html
spanDelimitedCode' block tree = treeToHtml (sbText block) tree

treeToHtml :: T.Text -> SpanTree -> Html
treeToHtml source' tree =
  let tree' = fillTreeAndAddTrivialLeaves (T.unpack source') tree in
  treeToHtml' source' tree'

treeToHtml' :: T.Text -> SpanTree -> Html
treeToHtml' source' tree = case tree of
  Span (_, _, _) children ->
    let body' = foldMap (treeToHtml' source') children in
    H.span body' ! spanClass
  LeafSpan (l, r, _) ->
    let spanText = sliceText l r source' in
    H.span (highlightSyntax spanText) ! spanLeaf
  Trivia (l, r) ->
    let spanText = sliceText l r source' in
    highlightSyntax spanText
  where
    spanClass :: Attribute
    spanClass = At.class_ "code-span"

    spanLeaf :: Attribute
    spanLeaf = At.class_ "code-span-leaf"

srcCtxsToSpanInfos :: SourceBlock -> [SrcPosCtx] -> [SpanPayload]
srcCtxsToSpanInfos block ctxs =
  let blockOffset = sbOffset block in
  let ctxs' = L.sort ctxs in
  (0, maxBound, 0) : mapMaybe (convert' blockOffset) ctxs'
  where convert' :: Int -> SrcPosCtx -> Maybe SpanPayload
        convert' offset (SrcPosCtx (Just (l, r)) (Just spanId)) = Just (l - offset, r - offset, spanId + 1)
        convert' _ _ = Nothing

srcCtxsToTree :: SourceBlock -> [SrcPosCtx] -> Maybe SpanTree
srcCtxsToTree block ctxs = makeEmptySpanTree (srcCtxsToSpanInfos block ctxs)

renderSpans :: HasSourceInfo a => a -> SourceBlock -> Html
renderSpans x block =
  let x' = addSpanIds x in
  let ctxs = gatherSourceInfo x' in
  toHtml $ cdiv "code-block" $ spanDelimitedCode block ctxs

highlightSyntax :: T.Text -> Html
highlightSyntax s = foldMap (uncurry syntaxSpan) classified
  where classified = ignoreExcept $ parseit s (many (withSource classify) <* eof)

syntaxSpan :: T.Text -> StrClass -> Html
syntaxSpan s NormalStr = toHtml s
syntaxSpan s c = H.span (toHtml s) ! class_ (stringValue className)
  where
    className = case c of
      CommentStr  -> "comment"
      KeywordStr  -> "keyword"
      CommandStr  -> "command"
      SymbolStr   -> "symbol"
      TypeNameStr -> "type-name"
      IsoSugarStr -> "iso-sugar"
      WhitespaceStr -> "whitespace"
      NormalStr -> error "Should have been matched already"

data StrClass = NormalStr
              | CommentStr | KeywordStr | CommandStr | SymbolStr | TypeNameStr
              | IsoSugarStr | WhitespaceStr

classify :: Parser StrClass
classify =
       (try (char ':' >> lowerWord) >> return CommandStr)
   <|> (symbol "-- " >> manyTill anySingle (void eol <|> eof) >> return CommentStr)
   <|> (do s <- lowerWord
           return $ if s `elem` keyWordStrs then KeywordStr else NormalStr)
   <|> (upperWord >> return TypeNameStr)
   <|> try (char '#' >> (char '?' <|> char '&' <|> char '|' <|> pure ' ')
        >> lowerWord >> return IsoSugarStr)
   <|> (some symChar >> return SymbolStr)
   <|> (some space1 >> return WhitespaceStr)
   <|> (anySingle >> return NormalStr)

lowerWord :: Parser String
lowerWord = (:) <$> lowerChar <*> many alphaNumChar

upperWord :: Parser String
upperWord = (:) <$> upperChar <*> many alphaNumChar
