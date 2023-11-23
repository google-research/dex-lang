-- Copyright 2023 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

module SourceIdTraversal (getASTInfo) where

import qualified Data.Map.Strict as M
import Control.Monad.Reader
import Control.Monad.Writer.Strict

import Types.Source
import Types.Primitives

getASTInfo :: SourceBlock' -> ASTInfo
getASTInfo b = runTreeM (SrcId 0) $ visit b

type TreeM = ReaderT SrcId (Writer ASTInfo)

runTreeM :: SrcId -> TreeM () -> ASTInfo
runTreeM root cont = snd $ runWriter $ runReaderT cont root

enterNode :: SrcId -> TreeM a -> TreeM a
enterNode sid cont = do
  emitNode sid
  local (const sid) cont

emitNode :: SrcId -> TreeM ()
emitNode child = do
  parent <- ask
  tell $ ASTInfo (M.singleton child parent) (M.singleton parent [child])

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
    CBin _       l r -> visit l >> visit r
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
  visit (WithSrcs sid sids x) = enterNode sid $ mapM_ emitNode sids >> visit x

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
