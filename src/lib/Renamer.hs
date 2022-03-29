-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module Renamer (rename) where

import Control.DeepSeq (force)
import Control.Exception (bracket, evaluate)
import Control.Monad.Reader hiding (lift)
import Control.Monad.State.Strict hiding (lift)
import Control.Monad.Writer hiding (lift)
import Data.Foldable
import Data.Void
import System.IO (hClose, hGetContents, IOMode( ReadMode ), openFile)
import Text.Megaparsec hiding (Label, State, Token, tokens)
import Text.Megaparsec.Char hiding (space, eol)
import Text.Megaparsec.Char qualified as MP

import SpaceParser qualified as SP
import Util (onFst, onSnd)

-- The goal is a renaming tool that preserves indentation.

-- The one-file pipeline is
-- - Tokenize the file into a low-level representation that just knows
--   which things are names, non-name strings, and spaces.
-- - Interpret the tokenization as a `Block`, below, which knows about
--   indents (including indents that depend on the token lengths in
--   the previous line).
-- - Carry out the rename on the `Block`.
-- - Print out the new representation.
--
-- However, we load all the argument files first, to see whether the
-- new name already occurs among them.  If it does, the rename is not
-- safe.

rename :: String -> String -> [FilePath] -> IO ()
rename from to files = do
  parsed <- mapM parseFile files
  isGo <- and <$> (mapM ok $ zip files parsed)
  if isGo
    then mapM_ write $ zip files parsed
    else return ()
  where
    ok (_, (Left e)) = putStrLn e >> return False
    ok (fname, (Right ls)) = if any (any (== to)) ls
      then putStrLn (to ++ " occurs in " ++ fname ++", aborting") >> return False
      else return True
    write (fname, (Right ls)) =
      writeFile fname $ runRenderM $ render $ fmap rename' $ interpret $ ls
    rename' s | s == from = to
              | otherwise = s

-- === Representation ===

data Token a
  = Name a
  | BracketedName String a String
  | NoRename String
  | Space
  -- Set the indentation position of the next indented block, if any.
  -- The int gives the offset from the current position.
  | HangTo Int
  deriving (Show, Functor, Foldable, Traversable)

width :: TokenS -> Int
width (Name s) = length s
width (BracketedName pre s post) = length pre + length s + length post
width (NoRename s) = length s
width Space = 1
width (HangTo _) = 0

-- The [Block] holds blocks indented relative to this line, if any.
-- The first Block in that list has indentation given by the last
-- HangTo token in the line, the next Block by the previous HangTo
-- token, etc.  The default indentation is 2 spaces.
data Line a = Line [Token a] [Block a]
  deriving (Show, Functor, Foldable, Traversable)

-- TODO Get rid of the concept of blocks entirely and just use a
-- HangTo 0 token at the beginning of a line to represent "continue at
-- this indentation"?  (That could even be the default).

newtype Block a = Block [Line a]
  deriving (Show, Functor, Foldable, Traversable)

type TokenS = Token String
type LineS = Line String
type BlockS = Block String

-- === Rendering ===

-- The semantics of the representation are probably well understood
-- through the renderer: A `Block` means what it renders to.

class Monad m => Renderer m where
  indent :: m ()
  indented :: m a -> m a
  hangTo :: Int -> m ()
  emit :: String -> m ()

runRenderM :: RenderM () -> String
runRenderM action = concat $ snd $ runWriter $ flip runReaderT ""
  $ flip evalStateT (0, []) $ unRenderM $ action

class Render a where
  render :: (Renderer m) => a -> m ()

instance Render BlockS where
  render (Block ls) = mapM_ render ls

instance Render LineS where
  render (Line ts blocks) = do
    indent
    mapM_ render ts
    -- TODO Status quo is that the EOL substring is the last Token (that
    -- way, we can preserve it).  An alternative would be to exclude
    -- them from the Tokens and explicitly emit an EOL here.  Yet
    -- another alternative would be to `unlines` the result of the
    -- writer instead.
    mapM_ (indented . render) blocks

instance Render TokenS where
  render (Name s) = emit s
  render (BracketedName pre s post) = emit pre >> emit s >> emit post
  render (NoRename s) = emit s
  render Space = emit " "
  render (HangTo offset) = hangTo offset

-- === Rendering monad ===

type Indentation = String

newtype RenderM a = RenderM
  -- The state is the current absolute position in the line, and the
  -- current stack of absolute hanging indentation targets.
  -- TODO: Is saying `tell [s]` to Writer [String] going to be efficient?
  { unRenderM :: (StateT (Int, [Int]) (ReaderT Indentation (Writer [String])) a) }
  deriving (Functor, Applicative, Monad)

instance Renderer RenderM where
  indent = (RenderM $ (modify $ onFst $ const 0) >> ask) >>= emit
  indented (RenderM action) = RenderM $ do
    hang_stack <- gets snd
    target <- case hang_stack of
      (target:rest) -> do
        modify $ onSnd $ const rest
        return target
      [] -> return 0  -- Default indentation
    local (padTo target) action
  hangTo target = RenderM $ do
    pos <- gets fst
    modify $ onSnd $ (:) $ pos + target
  emit s = RenderM $ do
    tell [s]
    modify $ onFst $ (+ (length s))

padTo :: Int -> String -> String
padTo w s = s ++ replicate (w - (length s)) ' '

-- === Parsing ===

type Parser = (Parsec Void String)

data RawLine a = RawLine Indentation [Token a]
  deriving (Show, Functor, Foldable, Traversable)

type RawLineS = RawLine String

instance Render RawLineS where
  render (RawLine indentation ts) = emit indentation >> mapM_ render ts

parseFile :: FilePath -> IO (Either String [RawLineS])
parseFile fname = do
  content <- readFile' fname
  let res = parseit fname content file
  return res

-- TODO Delete in favor of Prelude.readFile' (!) when we upgrade to
-- base-4.15.0.0 in stackage lts-19+
readFile' :: FilePath -> IO String
readFile' fn = bracket (openFile fn ReadMode) hClose $ \h ->
                       evaluate . force =<< hGetContents h

parseit :: FilePath -> String -> Parser a -> Either String a
parseit fname s p = case parse p fname s of
  Left e  -> Left $ errorBundlePretty e
  Right x -> return x

file :: Parser [RawLineS]
file = many ((fmap wrap proseBlock) <|> line) <* eof where
  wrap t = RawLine "" [t]

line :: Parser RawLineS
line = do
  echoLine <- optional echoedOutput
  case echoLine of
    (Just t) -> do
      end <- eol
      return $ RawLine "" $ [t, end]
    Nothing  -> do
      spc <- many $ char ' '
      ts <- many $ nonSpaceToken <|> space
      comment <- optional lineComment
      -- TODO: Unix pedantry: Allow lack of trailing newline at end of file.
      -- Just making eol optional here leads to an infinite parsing loop because
      -- it becomes possible to parse an empty RawLine without consuming any input.
      end <- eol
      return $ RawLine spc $ ts ++ (toList comment) ++ [end]

space :: Parser TokenS
space = Space <$ char ' '

eol :: Parser TokenS
eol = NoRename <$> MP.eol

nonSpaceToken :: Parser TokenS
nonSpaceToken = name <|> symName <|> backquoteName <|> literal <|> primName <|> punctuation

echoedOutput :: Parser TokenS
echoedOutput = do
  void $ char '>'
  content <- takeWhileP (Just "char") (/= '\n')
  return $ NoRename $ ">" ++ content  -- TODO Support renaming inside echoed outputs?

lineComment :: Parser TokenS
lineComment = do
  void $ string "--"
  content <- takeWhileP (Just "char") (/= '\n')
  return $ NoRename $ "--" ++ content  -- TODO Support renaming inside comments?

proseBlock :: Parser TokenS
proseBlock = do
  content <- SP.proseBlock
  return $ NoRename $ "'" ++ content  -- TODO Support renaming inside prose blocks?

name :: Parser TokenS
name = Name <$> (normalName <|> otherSym) where
  normalName = (:) <$> (lowerChar <|> upperChar) <*> many SP.nameTailChar

otherSym :: Parser String
otherSym = try $ do
  s <- some SP.symChar
  SP.failIf (s == "--") ""
  return s

symName :: Parser TokenS
symName = do
  s <- SP.symName
  return $ BracketedName "(" s ")"

backquoteName :: Parser TokenS
backquoteName = do
  s <- SP.backquoteName
  return $ BracketedName "`" s "`"

literal :: Parser TokenS
literal = charLit <|> strLit <|> intLit <|> doubleLit <|> unitCon

charLit :: Parser TokenS
charLit = noRenameToken SP.charLit

strLit :: Parser TokenS
strLit = noRenameToken SP.strLit

intLit :: Parser TokenS
intLit = noRenameToken SP.intLit

doubleLit :: Parser TokenS
doubleLit = noRenameToken SP.doubleLit

unitCon :: Parser TokenS
unitCon = noRenameToken SP.unitCon

primName :: Parser TokenS
primName = noRenameToken SP.primName

punctuation :: Parser TokenS
punctuation = noRenameToken $ SP.punctuation <|> char '#'

noRenameToken :: Parser a -> Parser TokenS
noRenameToken p = do
  (str, _) <- SP.withSource p
  return $ NoRename str

-- === Interpretation ===

-- Interpretation is understanding the indentation structure of a
-- [RawLine] and expressing it as a Block, which has the correct
-- nesting structure and HangTo tokens inserted in the correct
-- positions.

interpret :: [RawLineS] -> BlockS
interpret = extract . foldr addLine [] where
  extract [("", block)] = block
  -- If the staircase built out of a file has an indented leading
  -- block, collapse it one more time with a nominal RawLine that
  -- doesn't actually have any tokens.
  extract stair = extract $ addLine (RawLine "" []) stair
  -- I think this would be more
  -- elegant if we dispensed with blocks and used HangTo 0 to mean
  -- "continue indentation", because then gatherBlocks would
  -- return a value of the same type as this and we could just say
  --   extract = gatherBlocks (RawLine "" [])
  -- without further ado.

-- Interpretation proceeds back-to-front.  The tail of a source file
-- always looks like a staircase---a list of Blocks each of whose
-- leading Lines is indented strictly less than its predecessors:
--
--         code A
--           with sub-code in the Block
--     code B
--     more code B in the same Block
--   code C
--
-- We can add a line on top of this.  Every block indented strictly
-- more than that line becomes one of that line's sub-Blocks.  Then,
-- if there is a block indented exactly the same, this line becomes
-- the top of it, or if not, this line starts a new top Block.

type Staircase = [(Indentation, BlockS)]

addLine :: RawLineS -> Staircase -> Staircase
addLine raw@(RawLine indentation _) stair = attach ln stair' where
  attach :: LineS -> Staircase -> Staircase
  attach l [] = [(indentation, Block [l])]
  -- TODO Work out the logic of blocks with indentation starting at >
  -- and how they should interact with this staircase concept.
  -- The solution is probably a newtype with a custom ordering
  -- representing indentation.
  attach l (top@(ind2, (Block ls)):rest)
    | ind2 == indentation = (ind2, Block $ l:ls):rest
    | otherwise = (indentation, Block [l]):top:rest
  ln = gatherBlocks raw subBlocks
  (subBlocks, stair') = span nested stair
  nested (ind2, _) = length ind2 > length indentation

gatherBlocks :: RawLineS -> Staircase -> LineS
gatherBlocks (RawLine indentation raw_tokens) stair = Line tokens $ map snd stair where
  tokens = placeHangTos (prep (length indentation) raw_tokens []) (map fst stair) []
  -- The recursion is on the sequence of raw tokens in reverse,
  -- annotated with the absolute line position at the beginning of the
  -- token, and the stair in order.
  placeHangTos :: [(Int, TokenS)] -> [Indentation] -> [TokenS] -> [TokenS]
  placeHangTos [] [] ts' = ts'
  placeHangTos ((_, t):rest) [] ts' = placeHangTos rest [] $ t:ts'
  placeHangTos [] (ind:rest) ts' =
    placeHangTos [] rest $ (HangTo (length ind - length indentation)):ts'
  placeHangTos ((pos, t):ts) (ind:rest) ts'
    | length ind <= 4 = placeHangTos ts (ind:rest) $ t:ts'
    | pos > length ind = placeHangTos ts (ind:rest) $ t:ts'
    -- This case is a little weird.  I want to continue analyzing
    -- blocks at the current position, but I want the HangTo to appear
    -- in front of the current token in the result.  So I push the
    -- current token, and reconstruct my recursion with the HangTo in
    -- its place.
    | otherwise = placeHangTos ((pos, (HangTo (length ind - pos))):ts) rest $ t:ts'

  prep :: Int -> [TokenS] -> [(Int, TokenS)] -> [(Int, TokenS)]
  prep _ [] ts' = ts'
  prep pos (t:ts) ts' = prep (pos + width t) ts $ (pos, t):ts'
