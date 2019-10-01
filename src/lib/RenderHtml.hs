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
    classified = case parse (scanClassifier classify <* eof) "" s of
                   Left e -> error $ errorBundlePretty e
                   Right ans -> ans

syntaxSpan :: String -> Maybe StrClass -> Html
syntaxSpan s Nothing = toHtml s
syntaxSpan s (Just c) = H.span (toHtml s) ! class_ (stringValue className)
  where
    className = case c of
      CommentStr  -> "comment"  ; KeywordStr  -> "keyword"
      BuiltinStr  -> "builtin"  ; CommandStr  -> "command"
      SymbolStr   -> "symbol"   ; TypeNameStr -> "type-name"

data StrClass = CommentStr | KeywordStr | BuiltinStr
              | CommandStr | SymbolStr | TypeNameStr

scanClassifier :: Parser a -> Parser [(String, Maybe a)]
scanClassifier parser = many $ withSource (    liftM Just parser
                                           <|> (anySingle >> return Nothing))

classify :: Parser StrClass
classify =
       (char ':' >> many alphaNumChar >> return CommandStr)
   <|> (choice (map C.string keywords) >> return KeywordStr)
   <|> (choice (map C.string symbols ) >> return SymbolStr)
   -- TODO: the rest
  where
   keywords = ["for", "lam", "let", "in", "unpack", "pack"]
   symbols = ["+", "*", "/", "-", "^", "$", "@", ".", "::", "=", ">", "<"]

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
