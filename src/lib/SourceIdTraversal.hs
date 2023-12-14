-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module SourceIdTraversal (getGroupingInfo) where

import Control.Monad.Writer.Strict
import qualified Data.Map.Strict as M
import Data.Functor ((<&>))

import Types.Source
import Types.Primitives
import Err

getGroupingInfo :: SourceBlock' -> GroupingInfo
getGroupingInfo sb = groupTreeToGroupingInfo $ getGroupTree sb

groupTreeToGroupingInfo :: GroupTree -> GroupingInfo
groupTreeToGroupingInfo groupTreeTop = execWriter $ go Nothing groupTreeTop where
  go :: Maybe SrcId -> GroupTree -> Writer GroupingInfo ()
  go parent (GroupTree sid lexSpan children isAtomic) = do
    mapM_ (go (Just sid)) children
    let node = GroupTreeNode parent lexSpan (map gtSrcId children) isAtomic
    tell $ GroupingInfo $ M.singleton sid node

getGroupTree :: SourceBlock' -> GroupTree
getGroupTree b = mkGroupTree False rootSrcId $ runTreeM $ visit b

type TreeM = Writer [GroupTree]

mkGroupTree :: Bool -> SrcId -> [GroupTree] -> GroupTree
mkGroupTree isAtomic sid = \case
  [] -> GroupTree sid (sid,sid) [] isAtomic -- no children - must be a lexeme
  subtrees -> GroupTree sid (l,r) subtrees isAtomic
    where l = minimum $ subtrees <&> (fst . gtSpan)
          r = maximum $ subtrees <&> (snd . gtSpan)

runTreeM :: TreeM () -> [GroupTree]
runTreeM cont = snd $ runWriter $ cont

enterNode :: SrcId -> TreeM () -> TreeM ()
enterNode sid cont = tell [mkGroupTree False sid (runTreeM cont)]

emitLexeme :: SrcId -> TreeM ()
emitLexeme lexemeId = tell [mkGroupTree True lexemeId []]

class IsTree a where
  visit :: a -> TreeM ()

instance IsTree SourceBlock' where
  visit = \case
    TopDecl decl -> visit decl
    Command _ g -> visit g
    DeclareForeign v1 v2 g -> visit v1 >> visit v2 >> visit g
    DeclareCustomLinearization v _ g -> visit v >> visit g
    Misc _ -> return ()
    UnParseable _ _ -> return ()

instance IsTree Group where
  visit = \case
    CLeaf _ -> return ()
    CPrim _   xs -> mapM_ visit xs
    CParens   xs -> mapM_ visit xs
    CBrackets xs -> mapM_ visit xs
    CBin       b l r -> visit l >> visit b >> visit r
    CJuxtapose _ l r -> visit l >> visit r
    CPrefix      l r -> visit l >> visit r
    CGivens (x,y) -> visit x >> visit y
    CLambda args body -> visit args >> visit body
    CFor _ args body -> visit args >> visit body
    CCase scrut alts -> visit scrut >> visit alts
    CIf scrut ifTrue ifFalse -> visit scrut >> visit ifTrue >> visit ifFalse
    CDo body -> visit body
    CArrow l effs r -> visit l >> visit effs >> visit r
    CWith b body -> visit b >> visit body

instance IsTree Bin where
  visit = \case
    EvalBinOp b -> visit b
    _ -> return ()

instance IsTree CSBlock where
  visit = \case
    IndentedBlock sid decls -> enterNode sid $ visit decls
    ExprBlock body -> visit body

instance IsTree CSDecl where
  visit = \case
    CLet v rhs -> visit v >> visit rhs
    CDefDecl def -> visit def
    CExpr g -> visit g
    CBind v body -> visit v >> visit body
    CPass -> return ()

instance IsTree CTopDecl where
  visit = \case
    CSDecl _ decl -> visit decl
    CData v params givens cons -> visit v >> visit params >> visit givens >> visit cons
    CStruct v params givens fields methods -> visit v >> visit params >> visit givens >> visit fields >> visit methods
    CInterface v params methods -> visit v >> visit params >> visit methods
    CInstanceDecl def -> visit def

instance IsTree CDef where
  visit (CDef v params rhs givens body) =
    visit v >> visit params >> visit rhs >> visit givens >> visit body

instance IsTree CInstanceDef where
  visit (CInstanceDef v args givens methods name) =
    visit v >> visit args >> visit givens >> visit methods >> visit name

instance IsTree a => IsTree (WithSrc a) where
  visit (WithSrc sid x) = enterNode sid $ visit x

instance IsTree a => IsTree (WithSrcs a) where
  visit (WithSrcs sid sids x) = enterNode sid $ mapM_ emitLexeme sids >> visit x

instance IsTree a => IsTree [a] where
  visit xs = mapM_ visit xs

instance IsTree a => IsTree (Maybe a) where
  visit xs = mapM_ visit xs

instance (IsTree a, IsTree b) => IsTree (a, b) where
  visit (x, y) = visit x >> visit y

instance (IsTree a, IsTree b, IsTree c) => IsTree (a, b, c) where
  visit (x, y, z) = visit x >> visit y >> visit z

instance IsTree AppExplicitness where visit _ = return ()
instance IsTree SourceName      where visit _ = return ()
instance IsTree LetAnn          where visit _ = return ()
