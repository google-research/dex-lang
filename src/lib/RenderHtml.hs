{-# LANGUAGE OverloadedStrings #-}

module RenderHtml (renderLitProgHtml) where

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

renderLitProgHtml :: LitProg -> String
renderLitProgHtml blocks = renderHtml $ wrapBody $ mapM_ evalBlockHtml blocks

wrapBody :: Html -> Html
wrapBody inner = docTypeHtml $ do
  H.head $ do
    H.title "Output"
    H.link ! rel "stylesheet" ! href "style.css" ! type_ "text/css"
    H.meta ! charset "UTF-8"
    H.script mempty ! src "https://cdn.plot.ly/plotly-1.2.0.min.js"
  H.body $ H.div inner ! At.id "main-output"
  H.script mempty ! src "plot.js"

evalBlockHtml :: EvalBlock -> Html
evalBlockHtml evalBlock@(EvalBlock block result) =
  case sbContents block of
    ProseBlock s -> cdiv ("prose-block " ++ cellStatus)
                         (cdiv "prose-source" (mdToHtml s))
    EmptyLines -> return ()
    _ -> cdiv ("code-block " ++ cellStatus) $ do
           cdiv "code-source" (highlightSyntax (pprint block))
           resultHtml evalBlock
  where
    cellStatus = case result of
                   Left  _ -> "err-state"
                   Right _ -> "complete-state"

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

mdToHtml :: String -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] $ pack s

resultHtml :: EvalBlock -> Html
resultHtml evalBlock@(EvalBlock _ result) =
  case result of
    Right NoOutput -> mempty
    Right (ValOut Heatmap val) -> makeHeatmap val
    Right (ValOut Scatter val) -> makeScatter val
    _ -> cdiv "result-text" $ toHtml $ pprintResult False evalBlock

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
   keywords = ["for", "lam", "let", "in", "unpack", "pack", "type"]
   symbols = ["+", "*", "/", "-", "^", "$", "@", ".", "::", "=", ">", "<"]

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
  cdiv "heatmap" (dataDiv trace)
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
