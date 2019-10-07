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

import Syntax hiding (Heatmap)
import Record

data Scale = LinearScale Double Double

scatterHtml :: Value -> H.Html
scatterHtml (Value _ vecs) = diagramToHtml $
  position [(p2 (scaleToPlot xsc x, scaleToPlot ysc y), spot)
           | (x,y) <- zip xs ys]
  where
    RecTree (Tup [RecLeaf (RealVec xs), RecLeaf (RealVec ys)]) = vecs
    spot = circle 0.005 # fc blue # lw 0
    xsc = LinearScale (minimum xs) (maximum xs)
    ysc = LinearScale (minimum ys) (maximum ys)

heatmapHtml :: Value -> H.Html
heatmapHtml (Value ty vecs) = pngToHtml $ generateImage getPix w h
  where
    TabType (IdxSetLit h) (TabType (IdxSetLit w) _) = ty
    RecLeaf (RealVec zs) = vecs
    zsVec = V.fromList zs
    zScale = LinearScale (minimum zs) (maximum zs)
    getPix i j = greyPix zScale $ zsVec  V.! (j * w + i)

greyPix :: Scale -> Double -> PixelRGB8
greyPix scale_ x = PixelRGB8 px px px
  where px = fromIntegral $ doubleTo8Bit (1 - scaleToPlot scale_ x)

doubleTo8Bit :: Double -> Int
doubleTo8Bit x = min 255 $ max 0 (round (256 * x) :: Int)

scaleToPlot :: Scale -> Double -> Double
scaleToPlot (LinearScale low high) x = (x - low) / (high - low)

pngToHtml :: PngSavable a => Image a -> H.Html
pngToHtml png = H.img H.! At.class_ "plot-img" H.! At.src
  ("data:image/png;base64, " <> H.preEscapedTextValue encoded)
  where
    encoded = decodeUtf8 $ Base64.encode $ toStrict $ encodePng png

diagramToHtml :: Diagram B -> H.Html
diagramToHtml dia = pngToHtml (renderDia Rasterific opts dia)
  where
    opts = RasterificOptions (mkWidth 800)
