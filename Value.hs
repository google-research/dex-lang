{-# LANGUAGE GADTs #-}

module Value (Val, map) where

import qualified Data.Map.Strict as M
import Prelude hiding (map, lookup, flip)
import qualified Prelude as P
import Util

join :: Val -> Val
join (TabVal (TabTy k1 (TabTy k2 v)) m) =
    case checkEq k1 k2 of
        Nothing    -> error "Can't join on different keys"
        Just Equal -> TabVal (TabTy k1 v) (join' m)

flip :: Val -> Val
flip (TabVal (TabTy k1 (TabTy k2 v)) m) =
  let outTy = TabTy k2 (TabTy k1 v)
  in TabVal outTy (flip' m)

map :: (Val -> Val) -> Val -> Val
map f (TabVal (TabTy k v) m) =

map :: Val -> Val -> Val
map (ArrVar (ArrTy v1 v2) f) (TabVal (TabTy k v1) m) =
    TabVal (TabTy k v2) (map' f m)


map2 :: (Val -> Val -> Val) -> Val -> Val -> Val
map2 = undefined

reduce :: (Val -> Val -> Val) -> Val -> Val -> Val
reduce = undefined

data Equal a b where
  Equal :: Equal c c

checkEq :: Ty a -> Ty b -> Maybe (Equal a b)
checkEq IntTy IntTy = Just Equal
checkEq (TabTy a1 a2) (TabTy b1 b2) = do
    Equal <- checkEq a1 b1
    Equal <- checkEq a2 b2
    return Equal

data Ty t where
  IntTy :: Ty Int
  TabTy :: Ty a -> Ty b -> Ty (MMap a b)
  ArrTy :: Ty a -> Ty b -> Ty (a -> b)

data Val where
  IntVal :: Int -> Val
  TabVal :: Ty (MMap a b) -> MMap a b -> Val
  ArrVal :: Ty (a -> b) -> a -> b -> Val

-- Int
--          | TableVal


--          | TableVal Depth (T.Table Val Val)
--          | LamVal ValEnv IEnv Expr
--          | Builtin BuiltinName [Val]

-- -- ----- operations on maps -----

data MMap k v = MMap (M.Map k v) | Always v

join' :: MMap k (MMap k v) -> MMap k v
join' = undefined

flip' :: MMap k1 (MMap k2 v) -> MMap k2 (MMap k1 v)
flip' = undefined

map' :: (a -> b) -> MMap k a -> MMap k b
map' f (Always v) = Always $ f v
map' f (MMap m) = MMap $ M.map f m

map2' :: Ord k => (a -> b -> c) -> MMap k a -> MMap k b -> MMap k c
map2' f (Always x) (Always y) = Always $ f x y
map2' f (Always x) (MMap  my) = MMap $ M.map (f x) my
map2' f (MMap  mx) (Always y) = MMap $ M.map (P.flip f $ y) mx
map2' f (MMap  mx) (MMap  my) = MMap $ M.intersectionWith f mx my

reduce' :: (v -> v -> v) -> v -> MMap k v -> v
reduce' f z (Always x) = error "Can't reduce infinite map"
reduce' f z (MMap mx ) = M.foldr f z mx
