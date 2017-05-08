-- Another go at this problem:
-- https://github.com/sjoerdvisscher/blog/blob/master/2012/2012-03-03%20how%20to%20work%20generically%20with%20mutually%20recursive%20datatypes.md
{-# LANGUAGE TypeSynonymInstances, TypeApplications, FlexibleInstances, FlexibleContexts, DeriveGeneric #-}

import GHC.Generics
import Generics.OneLiner

data Decl = Var := Expr
          | Seq Decl Decl
          deriving (Eq, Show, Generic)

data Expr = Con Int
          | Add Expr Expr
          | Mul Expr Expr
          | EVar Var
          | Let Decl Expr
          deriving (Eq, Show, Generic)

type Var = String

class Vars t where
  vars :: t -> [Var] -> ([Var], [Var])

varsDefault :: (ADT t, Constraints t Vars) => t -> [Var] -> ([Var], [Var])
varsDefault = gfoldMap @Vars vars

instance Vars Var where
  vars v = const ([], [v])
instance Vars Decl where
  vars = varsDefault
instance Vars Int where
  vars = mempty
instance Vars Expr where
  vars (EVar v) = \bound -> (if (v `elem` bound) then [] else [v], [])
  vars (Let d e) = \bound ->
    let
      (freeD, declD) = vars d bound
      (freeE, _)     = vars e (declD ++ bound)
    in
      (freeD ++ freeE, [])
  vars x = varsDefault x

freeVars :: Vars t => t -> [Var]
freeVars = fst . ($ []) . vars

test :: [Var]
test = freeVars $ Let ("x" := Con 42) (Add (EVar "x") (EVar "y"))
