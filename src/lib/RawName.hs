-- Copyright 2022 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BinaryLiterals #-}

module RawName
  ( RawName, NameHint, HasNameHint (..), RawNameMap, noHint
  , rawNameFromHint, rawNames, freshRawName, lookup, singleton, restrictKeys
  , keys, elems, mapWithKey, unionWith, difference, intersection
  , fromList, toList, RawName.null, insert, traverseWithKey
  , member, disjoint, containedIn, adjust) where

import Prelude hiding (lookup)
import qualified Data.IntMap.Lazy as M
import qualified Data.IntSet as S
import Data.Hashable
import Data.Char
import Data.Bits
import Data.Coerce
import Data.Store
import Data.Text.Prettyprint.Doc  hiding (nest)
import GHC.Generics (Generic)
import Data.String

-- === RawName ===

-- While every name is represented using a single Integer, we treat its value
-- as a tagged union of two flavors distinguished by the most significant bit.
--
-- Note that the code below should generally be independent of the bit width
-- of Int (e.g. should work on both 32- and 64-bit sytems), but it does assume
-- an Int representation in 2's-complement (e.g. we assume that all silent names
-- compare as larger than all string names).
--
-- ~~~  Silent names: most significant bit = 0  ~~~
--
-- Silent names are basically 63-bit integers with no text component. Since the
-- tag is zero, the full value can be considered to be the integer identifying
-- the current name. That's it!
--
-- All silent names print as v123456 (for 123456 being the name value).
--
-- ~~~  String names: most significant bit = 1  ~~~
--
-- It is often helpful to associate some textual information with our names,
-- but they're used in so many places that simply increasing their size already
-- causes a non-negligible impact on performance. As a middle ground, we use
-- string names, which use their least significant byte as a counter and all
-- preceding bytes as storage for ASCII characters.
--
-- Taking a 32-bit system as an example, a string name will have capacity for
-- up to 3 characters. To support strings of varying length we use the most
-- significant bit of every character byte to indicate whether that character
-- field is empty (ASCII values fit into 7 bits). That is, every character byte
-- is a tagged union itself, with tag indicating presence of a value in the 7
-- least significant bits.
--
-- For example, a string ab with a counter of 4 can be encoded as follows:
--
--    byte 3    |    byte 2    |    byte 1    |    byte 0    |
--   1PPPPPPP   |   XPPPPPPP   |   XPPPPPPP   |   CCCCCCCC   |
--   11100001   |   11100010   |   00000000   |   00000100   |
--   ^- name tag    ^- present     ^- character missing
--    _______        _______        _______       ________
--   ASCII 'a'      ASCII 'b'       unused     8-bit unsigned
--
-- Note that the tag for the whole name bit also functions as a tag indicating
-- the presence of a character! As follows, string names require the presence
-- of at least one character.
--
-- The counter is used to easily generate fresh names based on the string seed.
-- Once all all counter values for a single string are in scope, fresh name
-- generation falls back to silent names.

type NameRep = Int

nameKindBit :: Int
nameKindBit = nameRepBits - 1

nameRepBits :: Int
nameRepBits = finiteBitSize @NameRep undefined

isStringName :: NameRep -> Bool
isStringName n = n `testBit` nameKindBit

stringNameStringMask :: NameRep
stringNameStringMask = complement stringNameCounterMask

stringNameCounterMask :: NameRep
stringNameCounterMask = 0xFF

stringNameString :: NameRep -> NameRep
stringNameString = (.&.) stringNameStringMask

firstSilentName :: NameRep
firstSilentName = zeroBits

lastSilentName :: NameRep
lastSilentName = complement zeroBits `clearBit` nameKindBit

newtype NameHint = NameHint Int
newtype RawName  = RawName  Int deriving (Eq, Ord, Generic, Hashable, Store)

freshRawName :: NameHint -> RawNameMap a -> RawName
freshRawName (NameHint hint) usedNames = RawName $! case isStringName hint of
  False -> freshSilentName
  True  -> case M.lookupLE maxWithHint usedNames of
    Nothing     -> hintString  -- empty Map
    Just (i, _) ->
      case stringNameString i == hintString of
        False -> hintString  -- no entries with current string
        True  -> case i .&. stringNameCounterMask == stringNameCounterMask of
          True  -> freshSilentName  -- fall back to silent names on counter overflow
          False -> i + 1
    where
      !maxWithHint = hint .|. stringNameCounterMask
      !hintString = stringNameString hint
  where
    freshSilentName = case M.lookupMax usedNames of
      Nothing     -> firstSilentName
      Just (i, _) -> case isStringName i of
        True  -> firstSilentName
        False -> case i == lastSilentName of
          False -> i + 1
          True  -> error "Ran out of numbers!"
    {-# INLINE freshSilentName #-}

rawNameFromHint :: NameHint -> RawName
rawNameFromHint = coerce

-- Names are guaranteed to be distinct from each other
rawNames :: Int -> [RawName]
rawNames n = [ RawName $! (firstSilentName + i) | i <- [0..(n-1)] ]

-- === conversion to/from strings ===

noHint :: NameHint
noHint = NameHint firstSilentName

class HasNameHint a where
  getNameHint :: a -> NameHint

instance HasNameHint RawName where
  getNameHint (RawName name) = NameHint name

instance HasNameHint String where
  getNameHint = hintFromString

instance IsString NameHint where
  fromString = hintFromString

hintFromString :: String -> NameHint
hintFromString s = NameHint $ goFromString (nameRepBits - 8) zeroBits s'
  where
    s' = case s of [] -> "v"; _ -> s

    goFromString :: Int -> NameRep -> String -> NameRep
    goFromString !shft !hint str = case shft > 0 of
      False -> hint
      True  -> goFromString (shft - 8) hint' str'
        where
          (hBits, str') = case str of
            []    -> (zeroBits, str)
            (h:t) -> (fromEnum (if isNiceAscii h then h else '_') .|. 0x80, t)
          hint' = hint .|. (hBits `shiftL` shft)
          isNiceAscii h = isAsciiLower h || isAsciiUpper h || isDigit h

instance HasNameHint a => HasNameHint (Maybe a) where
  getNameHint (Just x) = getNameHint x
  getNameHint (Nothing) = noHint

instance Pretty RawName where
  pretty = unsafeViaShow

instance Show RawName where
  show (RawName n) = case isStringName n of
    True  -> showStringName n
    False -> 'v' : '#' : show (n `clearBit` nameKindBit)

showStringName :: NameRep -> String
showStringName rep = go 8 $ case rep .&. stringNameCounterMask of
    0       -> []
    counter -> '.' : show counter
  where
    go !byteOff acc = case byteOff >= nameRepBits of
      True  -> acc
      False -> go (byteOff + 8) acc'
        where
          charByte = (rep `shiftR` byteOff) .&. 0xFF
          acc' = case charByte `testBit` 7 of
            False -> acc
            True  -> toEnum (charByte `clearBit` 7) : acc

instance Show NameHint where
  show (NameHint n) = show $ RawName n

-- === name map ===

type RawNameMap a = M.IntMap a

keys :: RawNameMap a -> [RawName]
keys m = coerce $ M.keys m

elems :: RawNameMap a -> [a]
elems m = coerce $ M.elems m

lookup :: RawName -> RawNameMap a -> Maybe a
lookup i m = M.lookup (coerce i) m

insert :: RawName -> a -> RawNameMap a -> RawNameMap a
insert i v m = M.insert (coerce i) v m

singleton :: RawName -> a -> RawNameMap a
singleton i x = M.singleton (coerce i) x

restrictKeys :: RawNameMap a -> [RawName] -> RawNameMap a
restrictKeys m xs = M.restrictKeys m (S.fromList $ coerce xs)

mapWithKey :: (RawName -> a -> b) -> RawNameMap a -> RawNameMap b
mapWithKey f m = M.mapWithKey (coerce f) m

unionWith :: (a -> a -> a) -> RawNameMap a ->  RawNameMap a -> RawNameMap a
unionWith f m1 m2 = M.unionWith (coerce f) m1 m2

difference :: RawNameMap a -> RawNameMap b -> RawNameMap a
difference m1 m2 = M.difference m1 m2

intersection :: RawNameMap a -> RawNameMap b -> RawNameMap a
intersection m1 m2 = M.intersection m1 m2

fromList :: [(RawName, a)] -> RawNameMap a
fromList xs = M.fromList (coerce xs)

toList :: RawNameMap a -> [(RawName, a)]
toList m = coerce $ M.toList m

member :: RawName -> RawNameMap a -> Bool
member i m = M.member (coerce i) m

disjoint :: RawNameMap a -> RawNameMap b -> Bool
disjoint m1 m2 = M.disjoint m1 m2

containedIn :: RawNameMap a -> RawNameMap b -> Bool
containedIn m1 m2 = M.null $ M.difference m1 m2

adjust :: (a -> a) -> RawName -> RawNameMap a -> RawNameMap a
adjust f i m = M.adjust f (coerce i) m

null :: RawNameMap a -> Bool
null = M.null

traverseWithKey :: Applicative t => (RawName -> a -> t b) -> RawNameMap a -> t (RawNameMap b)
traverseWithKey f m = M.traverseWithKey (coerce f) m
