-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Functions
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
{-# LANGUAGE RankNTypes, ConstraintKinds, ScopedTypeVariables #-}
module Generics.OneLiner.Functions (
  -- * For all instances
    eqADT
  , compareADT
  , minBoundADT
  , maxBoundADT
  , showsPrecADT
  , readPrecADT
  -- * For datatypes with one constructor
  , memptyADT
  , mappendADT
  , fromIntegerADT
  ) where

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

compareADT :: (ADT t, Constraints t Ord) => t -> t -> Ordering
compareADT s t = compare (ctorIndex s) (ctorIndex t) <>
  mbuilds (For :: For Ord) (\fld -> compare (s ! fld) (t ! fld)) `at` s

minBoundADT :: (ADT t, Constraints t Bounded) => t
minBoundADT = head $ builds (For :: For Bounded) (const minBound)

maxBoundADT :: (ADT t, Constraints t Bounded) => t
maxBoundADT = last $ builds (For :: For Bounded) (const maxBound)

showsPrecADT :: forall t. (ADT t, Constraints t Show) => Int -> t -> ShowS
showsPrecADT d t = inner fty
  where
    CtorInfo name rec fty = ctorInfo t (ctorIndex t)

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
    ctorReads = ctorParse <$> zip (fmap (ctorInfo (undefined :: t)) [0..]) (buildsA (For :: For Read) fieldParse)

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


memptyADT :: (ADTRecord t, Constraints t Monoid) => t
memptyADT = op0 (For :: For Monoid) mempty

mappendADT :: (ADTRecord t, Constraints t Monoid) => t -> t -> t
mappendADT = op2 (For :: For Monoid) mappend

fromIntegerADT :: (ADTRecord t, Constraints t Num) => Integer -> t
fromIntegerADT i = op0 (For :: For Num) (fromInteger i)
