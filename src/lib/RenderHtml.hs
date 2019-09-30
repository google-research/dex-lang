{-# LANGUAGE OverloadedStrings #-}

module RenderHtml (renderLitProgHtml) where

import Text.Blaze.Html5 as H
import Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.String

import Syntax
import PPrint

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
                         (cdiv "prose-source" (toHtml s))
    EmptyLines -> return ()
    _ -> cdiv ("code-block " ++ cellStatus) $ do
           cdiv "code-source" (toHtml (pprint block))
           cdiv "result-text" (toHtml (pprintResult False evalBlock))
  where
    cellStatus = case result of
                   Left  _ -> "err-state"
                   Right _ -> "complete-state"

cdiv :: String -> Html -> Html
cdiv c inner = H.div inner ! class_ (stringValue c)
