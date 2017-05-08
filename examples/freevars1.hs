-- Another go at this problem:
-- https://github.com/sjoerdvisscher/blog/blob/master/2012/2012-03-03%20how%20to%20work%20generically%20with%20mutually%20recursive%20datatypes.md
{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveGeneric, TypeApplications, ScopedTypeVariables, MultiParamTypeClasses #-}

import GHC.Generics
import Generics.OneLiner

data Decl a b = a := Expr a b
              | Seq (Decl a b) (Decl a b)
              deriving (Eq, Show, Generic1)

data Expr a b = Con Int
              | Add (Expr a b) (Expr a b)
              | Mul (Expr a b) (Expr a b)
              | EVar b
              | Let (Decl a b) (Expr a b)
              deriving (Eq, Show, Generic1)

class Vars a t where
  vars1 :: (b -> [a] -> ([a], [a])) -> t b -> [a] -> ([a], [a])

vars1Default :: forall a b t. (ADT1 t, Constraints1 t (Vars a)) => (b -> [a] -> ([a], [a])) -> t b -> [a] -> ([a], [a])
vars1Default = gfoldMap1 @(Vars a) vars1

instance Vars a (Decl a) where
  vars1 f (v := e) = const ([], [v]) `mappend` vars1 f e
  vars1 f x = vars1Default f x
instance Vars a (Expr a) where
  vars1 f (Let d e) = \bound ->
    let
      (freeD, declD) = vars1 f d bound
      (freeE, _)     = vars1 f e (declD ++ bound)
    in
      (freeD ++ freeE, [])
  vars1 f x = vars1Default f x

freeVars :: (Eq a, Vars a t) => t a -> [a]
freeVars = fst . ($ []) . vars1 (\v bound -> (if (v `elem` bound) then [] else [v], []))

test :: [String]
test = freeVars $ Let (Seq ("x" := Con 42) ("q" := EVar "z")) (Add (EVar "x") (EVar "y"))
