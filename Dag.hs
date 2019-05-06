module Dag (Dag, dagInsert, dagDelete, ancestors, descendents,
            children, parents) where

import Data.Foldable (toList)
import Data.Maybe (fromJust)
import Control.Monad.State
import qualified Data.Map.Strict as M
import qualified Data.Set as Set

newtype Dag k = Dag (M.Map k ([k], [k]))

dagInsert :: Ord k => k -> [k] -> Dag k -> Dag k
dagInsert k parents (Dag m) = Dag $ M.insert k (parents, []) m

-- cascades to children and returns invalidated nodes (including this node)
dagDelete :: Ord k => k -> Dag k -> (Dag k, [k])
dagDelete k dag@(Dag m) = (Dag (foldr M.delete m invalid), invalid)
  where invalid = k : descendents k dag

ancestors :: Ord k => k -> Dag k -> [k]
ancestors k dag = toList (Set.delete k reachable)
  where reachable = execState (reachableSet (flip parents dag) k) mempty

descendents :: Ord k => k -> Dag k -> [k]
descendents k dag = toList (Set.delete k reachable)
  where reachable = execState (reachableSet (flip children dag) k) mempty

children :: Ord k => k -> Dag k -> [k]
children k (Dag m) = fst $ fromJust (M.lookup k m)

parents :: Ord k => k -> Dag k -> [k]
parents k (Dag m) = snd $ fromJust (M.lookup k m)

reachableSet :: Ord k => (k -> [k]) -> k -> State (Set.Set k) ()
reachableSet getNext k = do
  visited <- gets (Set.member k)
  if visited then return ()
             else do modify (Set.insert k)
                     mapM_ (reachableSet getNext) (getNext k)
