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
  H.div (srcDiv <> outDiv) ! class_ cellStatus
  where
    srcDiv = H.div (toHtml (pprint block)) ! class_ "source"
    outDiv = H.div (toHtml (pprintResult False evalBlock)) ! class_ "result-text"
    cellStatus = case result of
                   Left  _ -> "err-cell"
                   Right _ -> "complete-cell"
