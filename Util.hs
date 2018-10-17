module Util (group, ungroup, unJust, pad, padLeft, delIdx, replaceIdx,
             insertIdx, mvIdx, mapFst, mapSnd, splitWhile, repeatN,
             composeN, mapMaybe) where


group :: (Ord a) => [(a,b)] -> [(a, [b])]
group [] = []
group ((k,v):rem) =
  let (prefix, suffix) = splitWhile ((== k) . fst) rem
      g = v:(map snd prefix)
  in (k, g) : group suffix

ungroup ::  [(a, [b])] -> [(a,b)]
ungroup [] = []
ungroup ((k,vs):rem) = (zip (repeat k) vs) ++ ungroup rem

unJust :: Maybe a -> a
unJust (Just x) = x
unJust Nothing = error "whoops!"

pad :: Int -> a -> [a] -> [a]
pad n v xs = xs ++ repeatN (n - length(xs)) v

padLeft :: Int -> a -> [a] -> [a]
padLeft  n v xs = repeatN (n - length(xs)) v ++ xs

delIdx :: Int -> [a] -> [a]
delIdx i xs = case splitAt i xs of
  (prefix, x:suffix) -> prefix ++ suffix

replaceIdx :: Int -> a -> [a] -> [a]
replaceIdx i x xs = case splitAt i xs of
  (prefix, _:suffix) -> prefix ++ (x:suffix)

insertIdx :: Int -> a -> [a] -> [a]
insertIdx i x xs = case splitAt i xs of
  (prefix, suffix) -> prefix ++ (x:suffix)

mvIdx :: Int -> Int -> [a] -> [a]
mvIdx i j xs | j == i = xs
             | j < i = let x = xs!!i
                       in insertIdx j x . delIdx i $ xs

mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f zs = [(f x, y) | (x, y) <- zs]

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f zs = [(x, f y) | (x, y) <- zs]

mapMaybe :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f [] = []
mapMaybe f (x:xs) = let rest = mapMaybe f xs
                    in case f x of
                        Just y  -> y : rest
                        Nothing -> rest

splitWhile :: (a -> Bool) -> [a] -> ([a], [a])
splitWhile f xs = (takeWhile f xs, dropWhile f xs)

repeatN :: Int -> a -> [a]
repeatN n x = take n (repeat x)

composeN :: Int -> (a -> a) -> a -> a
composeN n f = foldr (.) id (repeatN n f)
