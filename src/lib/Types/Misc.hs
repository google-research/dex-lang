-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Types.Misc where

import GHC.Generics (Generic (..))

import Err
import Logging
import Types.Source

type LitProg = [(SourceBlock, Result)]

data Result = Result
                { resultOutputs :: [Output]
                , resultErrs    :: Except () }
              deriving (Show, Eq)

type BenchStats = (Int, Double) -- number of runs, total benchmarking time
data Output =
    TextOut String
  | HtmlOut String
  | PassInfo PassName String
  | EvalTime  Double (Maybe BenchStats)
  | TotalTime Double
  | BenchResult String Double Double (Maybe BenchStats) -- name, compile time, eval time
  | MiscLog String
  -- Used to have | ExportedFun String Atom
    deriving (Show, Eq, Generic)

type PassLogger = FilteredLogger PassName [Output]

data OptLevel = NoOptimize | Optimize

instance Semigroup Result where
  Result outs err <> Result outs' err' = Result (outs <> outs') err''
    where err'' = case err' of
            Success () -> err
            Failure _  -> err'

instance Monoid Result where
  mempty = Result mempty (Success ())
