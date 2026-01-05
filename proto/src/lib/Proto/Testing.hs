-- Copyright 2025 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Proto.Testing where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C

import Control.Monad
import Proto.Util
import Proto.Doc
import Proto.Monad

runTest :: TestCase -> (ByteString -> ProtoM r ()) -> ProtoM r ()
runTest test runit = do
  withLogBlock PlainBlock do
    logM $ oneLiner $ test.name
    (_, result) <- captureLog $ runit test.source
    resultStr <- doc2Str result
    indented do
      if str2bs resultStr == test.expectedResult
        then logM $ oneLiner "OK"
        else withLogBlock ErrorBlock do
          logM do
            oneLiner "Expected:"
            indented $ multiLiner $ bs2str test.expectedResult
            oneLiner "Got:"
            indented $ multiLiner resultStr

data Tests = Tests {
  prelude :: ByteString,
  cases   :: [TestCase]}

type TestName = String
data TestCase = TestCase {
  name           :: TestName,
  lineNum        :: Int,
  source         :: ByteString,
  expectedResult :: ByteString}

data Line =
   HeaderLine TestName
 | ResultLine ByteString  -- excludes "> "
 | EmptyLine ByteString  -- includes comments
 | OtherLine ByteString

-- === parsing test files ===

parseTestFile :: ByteString -> ProtoM r Tests
parseTestFile s = do
  lineNum <- newRef 0
  remaining <- newStack $ getLines s
  liftProtoM (\_ -> TestParserCtx lineNum remaining) parseTests

data TestParserCtx = TestParserCtx {
  lineNum   :: Ref Int,
  remaining :: Stack Line }

type TestParser = ProtoM TestParserCtx

parseTests :: TestParser Tests
parseTests = Tests <$> parseSourceCode <*> takeWhileJust tryTestCase

getLines :: ByteString -> [Line]
getLines s = map parseLine $ C.lines s

parseLine :: ByteString -> Line
parseLine s = case BS.indexMaybe s 0 of
  Nothing -> EmptyLine s
  Just c -> case w2c c of
    '>' -> ResultLine $ BS.drop 2 s
    '#' -> EmptyLine s
    '%' -> HeaderLine $ parseTestData $ bs2str s
    _ -> OtherLine s

-- TODO: allow for cmd line args etc in test header
parseTestData :: String -> TestName
parseTestData s = drop 2 s

tryTestCase :: TestParser (Maybe TestCase)
tryTestCase = do
  lineNum <- curLineNum
  nextLine >>= \case
    Just (HeaderLine name) -> do
      source <- parseSourceCode
      expectedResult <- parseExpectedResult
      skipEmpties
      return $ Just $ TestCase name lineNum source expectedResult
    Just _ -> throw $ oneLiner "Expected a test case"
    Nothing -> return Nothing

parseSourceCode :: TestParser ByteString
parseSourceCode = do
  C.unlines <$> takeMany \case
    OtherLine line -> Just line
    EmptyLine line -> Just line
    _ -> Nothing

parseExpectedResult :: TestParser ByteString
parseExpectedResult = do
  C.unlines <$> takeMany \case
    ResultLine line -> Just line
    _ -> Nothing

skipEmpties :: TestParser ()
skipEmpties = void do
  takeMany \case
    EmptyLine _ -> Just ()
    _ -> Nothing

takeMany :: (Line -> Maybe a) -> TestParser [a]
takeMany f = peekLine >>= \case
  Nothing -> return []
  Just line -> case f line of
    Just x -> nextLine >> (x:) <$> takeMany f
    _ -> return []

takeWhileJust :: TestParser (Maybe a) -> TestParser [a]
takeWhileJust p = do
  p >>= \case
    Just x -> (x:) <$> takeWhileJust p
    Nothing -> return []

nextLine :: TestParser (Maybe Line)
nextLine = do
  c <- getCtx
  update c.lineNum (+ 1)
  pop c.remaining

peekLine :: TestParser (Maybe Line)
peekLine = getCtx >>= \c -> peek c.remaining

curLineNum :: TestParser Int
curLineNum = getCtx >>= \c -> get c.lineNum
