-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Functions
-- Copyright   :  (c) Sjoerd Visscher 2012
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
{-# LANGUAGE RankNTypes, ConstraintKinds, ScopedTypeVariables #-}
module Generics.OneLiner.Functions where

import Generics.OneLiner.ADT
import Control.Applicative
import Data.Monoid

import Text.Read
import Control.Monad
import Control.Monad.Trans.State
import qualified Control.Monad.Trans.Class as T

eqADT :: (ADT t, Constraints t Eq) => t -> t -> Bool
eqADT s t = ctorIndex s == ctorIndex t && 
  getAll (mbuilds (For :: For Eq) (\fld -> All $ s ! fld == t ! fld) `at` s)

cmpADT :: (ADT t, Constraints t Ord) => t -> t -> Ordering
cmpADT s t = ctorIndex s `compare` ctorIndex t <> 
  mbuilds (For :: For Ord) (\fld -> (s ! fld) `compare` (t ! fld)) `at` s

minBoundADT :: (ADT t, Constraints t Bounded) => t
minBoundADT = snd $ head $ builds (For :: For Bounded) (const minBound)

maxBoundADT :: (ADT t, Constraints t Bounded) => t
maxBoundADT = snd $ last $ builds (For :: For Bounded) (const maxBound)

showsPrecADT :: forall t. (ADT t, Constraints t Show) => Int -> t -> ShowS
showsPrecADT d t = inner fty
  where
    CtorInfo name rec fty = fst $ builds (For :: For Show) (t !) !! ctorIndex t

    inner (Infix _ d') = showParen (d > d') $ let [f0, f1] = fields (d' + 1) in 
      f0 . showChar ' ' . showString name . showChar ' ' . f1
    inner _ = showParen (d > 10) $ showString name . showChar ' ' . body

    body = if rec 
      then showChar '{' . conc (showString ", ") (fields 0) . showChar '}'
      else conc (showString " ") (fields 11)

    fields d' = mbuilds (For :: For Show) (return . f d') `at` t

    f :: Show s => Int -> FieldInfo (t -> s) -> ShowS
    f d' info = if rec 
      then showString (selectorName info) . showString " = " . showsPrec d' (t ! info)
      else showsPrec d' (t ! info)

    conc sep = foldr1 (\g ss -> g . sep . ss)

readPrecADT :: forall t. (ADT t, Constraints t Read) => ReadPrec t
readPrecADT = parens (choice ctorReads)
  where
    ctorReads = ctorParse <$> buildsA (For :: For Read) fieldParse

    ctorParse (CtorInfo name _ (Infix _ d), getFields) = 
      let flds = evalStateT getFields $ do { Symbol name' <- lexP; guard (name' == name) }
      in prec d flds

    ctorParse (CtorInfo name rec _, getFields) = 
      let flds = evalStateT getFields (return ())
      in prec (if rec then 11 else 10) $ do
        Ident name' <- lexP
        guard (name == name')
        if rec then do
            Punc "{" <- lexP
            res <- flds
            Punc "}" <- lexP
            return res
          else
            flds

    -- StateT is used to parse an infix operator after the first field
    fieldParse :: Read s => FieldInfo (t -> s) -> StateT (ReadPrec ()) ReadPrec s
    fieldParse (SelectorInfo name _) = StateT $ \parseOp -> do
      Ident name' <- lexP
      guard (name == name')
      Punc "=" <- lexP
      res <- reset readPrec
      parseOp
      return (res, return ())  
    fieldParse _ = StateT $ \parseOp -> do
      res <- step readPrec
      parseOp
      return (res, return ())
