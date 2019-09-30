{-# LANGUAGE OverloadedStrings #-}

module RenderHtml (renderLitProgHtml) where

import Text.Blaze.Html5 as H  hiding (map)
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.String
import Data.Text (pack)
import CMark (commonmarkToHtml)

import Control.Monad
import Text.Megaparsec
import Text.Megaparsec.Char as C

import Syntax
import PPrint
import ParseUtil

renderLitProgHtml :: LitProg -> String
renderLitProgHtml blocks = renderHtml $ wrapBody $ mapM_ evalBlockHtml blocks

wrapBody :: Html -> Html
wrapBody inner = docTypeHtml $ do
  H.head $ do
    H.title "Output"
    H.link ! rel "stylesheet" ! href "style.css" ! type_ "text/css"
    H.meta ! charset "UTF-8"
  H.body $ H.div inner ! A.id "main-output"

evalBlockHtml :: EvalBlock -> Html
evalBlockHtml evalBlock@(EvalBlock block result) =
  case sbContents block of
    ProseBlock s -> cdiv ("prose-block " ++ cellStatus)
                         (cdiv "prose-source" (mdToHtml s))
    EmptyLines -> return ()
    _ -> cdiv ("code-block " ++ cellStatus) $ do
           cdiv "code-source" (highlightSyntax (pprint block))
           cdiv "result-text" (toHtml (pprintResult False evalBlock))
  where
    cellStatus = case result of
                   Left  _ -> "err-state"
                   Right _ -> "complete-state"

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)

mdToHtml :: String -> Html
mdToHtml s = preEscapedText $ commonmarkToHtml [] $ pack s

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
