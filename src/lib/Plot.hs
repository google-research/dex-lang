-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE TypeFamilies              #-}

module Plot (scatterHtml, heatmapHtml) where

import Prelude as P
import Diagrams.Prelude
import Diagrams.Backend.Rasterific
import Data.ByteString.Lazy (toStrict)
import Data.Text.Encoding (decodeUtf8)
import qualified Data.ByteString.Base64 as Base64
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as At
import Codec.Picture.Png
import Codec.Picture.Types
import qualified Data.Vector as V

import Syntax

data Scale = LinearScale Double Double

scatterHtml :: Val -> H.Html
scatterHtml = undefined

-- scatterHtml (FlatVal _ arrays) = diagramToHtml $
--   position [(p2 (scaleToPlot xsc x, scaleToPlot ysc y), spot)
--            | (x,y) <- zip xs ys]
--   where
--     [Array _ (RealVecVal xs), Array _ (RealVec ys)] = arrays
--     spot = circle 0.005 # fc blue # lw 0
--     xsc = LinearScale (minimum xs) (maximum xs)
--     ysc = LinearScale (minimum ys) (maximum ys)

heatmapHtml :: Val -> H.Html
heatmapHtml = undefined
-- heatmapHtml (FlatVal _ ~[array]) = pngToHtml $ generateImage getPix w h
--   where
--     Array [h, w] (RealVecVal zs) = array
--     zsVec = V.fromList zs
--     zScale = LinearScale (minimum zs) (maximum zs)
--     getPix i j = greyPix zScale $ zsVec  V.! (j * w + i)

greyPix :: Scale -> Double -> PixelRGB8
greyPix scale_ x = PixelRGB8 px px px
  where px = fromIntegral $ doubleTo8Bit (1 - scaleToPlot scale_ x)

doubleTo8Bit :: Double -> Int
doubleTo8Bit x = min 255 $ max 0 (round (256 * x) :: Int)

scaleToPlot :: Scale -> Double -> Double
scaleToPlot (LinearScale low high) x = (x - low) / (high - low + 1e-6)

pngToHtml :: PngSavable a => Image a -> H.Html
pngToHtml png = H.img H.! At.class_ "plot-img" H.! At.src
  ("data:image/png;base64, " <> H.preEscapedTextValue encoded)
  where
    encoded = decodeUtf8 $ Base64.encode $ toStrict $ encodePng png

diagramToHtml :: Diagram B -> H.Html
diagramToHtml dia = pngToHtml (renderDia Rasterific opts dia)
  where
    opts = RasterificOptions (mkWidth 800)
