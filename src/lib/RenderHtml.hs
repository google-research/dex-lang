-- Copyright 2019 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     https://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module RenderHtml (pprintHtml, progHtml) where

import Text.Blaze.Html5 as H  hiding (map)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.Text (pack)
import CMark (commonmarkToHtml)

import Control.Monad
import Text.Megaparsec hiding (chunk)
import Text.Megaparsec.Char as C

import Syntax
import PPrint
import ParseUtil
import Plot

pprintHtml :: ToMarkup a => a -> String
pprintHtml x = renderHtml $ toMarkup x

progHtml :: LitProg -> String
progHtml blocks = renderHtml $ wrapBody $ map toHtmlBlock blocks
  where
    toHtmlBlock (block,result) = toMarkup block <> toMarkup result

wrapBody :: [Html] -> Html
wrapBody blocks = docTypeHtml $ do
  H.head $ do
    H.link ! rel "stylesheet" ! href "style.css" ! type_ "text/css"
    H.meta ! charset "UTF-8"
  H.body $ H.div inner ! At.id "main-output"
  where inner = foldMap (cdiv "cell") blocks

instance ToMarkup Result where
  toMarkup result = case result of
    Result (Left _) -> cdiv "err-block" $ toHtml $ pprint result
    Result (Right ans) -> case ans of
      NoOutput -> mempty
      ValOut Heatmap val -> cdiv "plot" $ heatmapHtml val
      ValOut Scatter val -> cdiv "plot" $ scatterHtml val
      _ -> cdiv "result-block" $ toHtml $ pprint result

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
  where
    classified = case parse (many (withSource classify) <* eof) "" s of
                   Left e -> error $ errorBundlePretty e
                   Right ans -> ans

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
      NormalStr -> error "Should have been matched already"

data StrClass = NormalStr
              | CommentStr | KeywordStr | CommandStr | SymbolStr | TypeNameStr

classify :: Parser StrClass
classify =
       (try (char ':' >> lowerWord) >> return CommandStr)
   <|> (symbol "--" >> manyTill anySingle (void eol <|> eof) >> return CommentStr)
   <|> (do s <- lowerWord
           return $ if s `elem` keywords then KeywordStr else NormalStr)
   <|> (symbol "A " >> return KeywordStr)
   <|> (symbol "E " >> return KeywordStr)
   <|> (upperWord >> return TypeNameStr)
   <|> (choice (map C.string symbols ) >> return SymbolStr)
   <|> (anySingle >> return NormalStr)
  where
   keywords = ["for", "lam", "let", "in", "unpack", "pack", "type", "todo"]
   symbols = ["+", "*", "/", "-", "^", "$", "@", ".", "::", ";", "=", ">", "<"]

lowerWord :: Parser String
lowerWord = (:) <$> lowerChar <*> many alphaNumChar

upperWord :: Parser String
upperWord = (:) <$> upperChar <*> many alphaNumChar
