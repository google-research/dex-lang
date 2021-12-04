-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module RenderHtml (pprintHtml, progHtml, ToMarkup) where

import Text.Blaze.Html5 as H  hiding (map)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.Text (pack)
import CMark (commonmarkToHtml)
import GHC.Exts (IsString (..))

import Control.Monad
import Text.Megaparsec hiding (chunk)
import Text.Megaparsec.Char as C

import Resources (cssSource, javascriptSource)
import Syntax
import PPrint
import Parser
import Serialize ()
import Err

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
    jsSource = fromString (javascriptSource ++ "render(RENDER_MODE.STATIC);")

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
    ProseBlock s -> cdiv "prose-block" $ mdToHtml s
    _ -> cdiv "code-block" $ highlightSyntax (pprint block)

mdToHtml :: String -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] $ pack s

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

-- === syntax highlighting ===

highlightSyntax :: String -> Html
highlightSyntax s = foldMap (uncurry syntaxSpan) classified
  where classified = ignoreExcept $ parseit s (many (withSource classify) <* eof)

syntaxSpan :: String -> StrClass -> Html
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
      NormalStr -> error "Should have been matched already"

data StrClass = NormalStr
              | CommentStr | KeywordStr | CommandStr | SymbolStr | TypeNameStr
              | IsoSugarStr

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
   <|> (anySingle >> return NormalStr)

lowerWord :: Parser String
lowerWord = (:) <$> lowerChar <*> many alphaNumChar

upperWord :: Parser String
upperWord = (:) <$> upperChar <*> many alphaNumChar
