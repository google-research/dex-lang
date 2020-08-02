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

import Control.Monad
import qualified Data.Vector.Storable as V
import Text.Megaparsec hiding (chunk)
import Text.Megaparsec.Char as C

import Syntax
import PPrint
import Parser
import Plot
import Serialize()

pprintHtml :: ToMarkup a => a -> String
pprintHtml x = renderHtml $ toMarkup x

progHtml :: LitProg -> String
progHtml blocks = renderHtml $ wrapBody $ map toHtmlBlock blocks
  where toHtmlBlock (block,result) = toMarkup block <> toMarkup result

wrapBody :: [Html] -> Html
wrapBody blocks = docTypeHtml $ do
  H.head $ do
    H.link ! rel "stylesheet" ! href "style.css" ! type_ "text/css"
    H.meta ! charset "UTF-8"
  H.body $ H.div inner ! At.id "main-output"
  where inner = foldMap (cdiv "cell") blocks

instance ToMarkup Result where
  toMarkup (Result outs err) = foldMap toMarkup outs <> err'
    where err' = case err of
                   Left e   -> cdiv "err-block" $ toHtml $ pprint e
                   Right () -> mempty

instance ToMarkup Output where
  toMarkup out = case out of
    HeatmapOut False h w zs -> heatmapHtml h w zs
    HeatmapOut True h w zs  -> colorHeatmapHtml h w zs
    ScatterOut xs ys  -> scatterHtml (V.toList xs) (V.toList ys)
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
  where
    classified = case runTheParser s (many (withSource classify) <* eof) of
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
   <|> (symbol "-- " >> manyTill anySingle (void eol <|> eof) >> return CommentStr)
   <|> (do s <- lowerWord
           return $ if s `elem` keyWordStrs then KeywordStr else NormalStr)
   <|> (upperWord >> return TypeNameStr)
   <|> (some symChar >> return SymbolStr)
   <|> (anySingle >> return NormalStr)

lowerWord :: Parser String
lowerWord = (:) <$> lowerChar <*> many alphaNumChar

upperWord :: Parser String
upperWord = (:) <$> upperChar <*> many alphaNumChar
