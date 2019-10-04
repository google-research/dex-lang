{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module RenderHtml (pprintHtml, progHtml) where

import Text.Blaze.Html5 as H  hiding (map)
import Text.Blaze.Html5.Attributes as At
import Text.Blaze.Html.Renderer.String
import Data.Text (pack)
import Data.ByteString.Lazy (unpack)
import CMark (commonmarkToHtml)
import Data.Aeson hiding (Result, Null, Value)
import qualified Data.Aeson as A
import Data.Char (chr)

import Control.Monad
import Text.Megaparsec hiding (chunk)
import Text.Megaparsec.Char as C

import Syntax
import PPrint
import ParseUtil
import Record

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
    H.script mempty ! src "https://cdn.plot.ly/plotly-1.2.0.min.js"
    H.script mempty ! src "plot.js"
  H.body $ do H.div inner ! At.id "main-output"
              H.script "render_plots()"
  where inner = foldMap (cdiv "cell") blocks

instance ToMarkup Result where
  toMarkup result = case result of
    Result (Left _) -> cdiv "err-block" $ toHtml $ pprint result
    Result (Right ans) -> case ans of
      NoOutput -> mempty
      ValOut Heatmap val -> makeHeatmap val
      ValOut Scatter val -> makeScatter val
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

-- === plotting ===

makeScatter :: Value -> Html
makeScatter (Value _ vecs) = cdiv "scatter" (jsonAsHtml trace)
  where
    trace :: A.Value
    trace = A.object
      [ "x" .= toJSON xs
      , "y" .= toJSON ys
      , "mode" .= toJSON ("markers"   :: A.Value)
      , "type" .= toJSON ("scatter" :: A.Value)
      ]
    RecTree (Tup [RecLeaf (RealVec xs), RecLeaf (RealVec ys)]) = vecs

dataDiv :: A.Value -> Html
dataDiv val = cdiv "data" (jsonAsHtml val) ! At.style "display: none;"

makeHeatmap :: Value -> Html
makeHeatmap (Value ty vecs) =
  cdiv "plot-pending" (dataDiv trace)
  where
    TabType _ (TabType (IdxSetLit n) _) = ty
    trace :: A.Value
    trace = A.object
      [ "z" .= toJSON (chunk n xs)
      , "type" .= toJSON ("heatmap" :: A.Value)
      , "colorscale" .= toJSON ("Greys" :: A.Value)
      ]
    RecLeaf (RealVec xs) = vecs

jsonAsHtml :: A.Value -> Html
jsonAsHtml val = toHtml $ map (chr . fromEnum) $ unpack $ encode val

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = row : chunk n rest
  where (row, rest) = splitAt n xs
