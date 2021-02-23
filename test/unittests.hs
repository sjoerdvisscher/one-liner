{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}

import Data.Functor.Identity
import GHC.Generics
import Test.HUnit
import Generics.OneLiner

data T a = T0 | T1 a | T2 a a deriving (Eq, Show, Generic, Generic1)
data Pair a = Pair a a deriving (Eq, Show, Generic, Generic1)

create0 :: (ADT t, Constraints t ((~) Int)) => [t]
create0 = create @((~) Int) [0]

testCreate :: Test
testCreate = "create" ~:
  [ "Identity" ~: create0 ~?= [Identity 0]
  , "()"       ~: create0 ~?= [()]
  , "(,)"      ~: create0 ~?= [(0, 0)]
  , "Either"   ~: create0 ~?= [Left 0, Right 0]
  , "Maybe"    ~: create0 ~?= [Nothing, Just 0]
  , "T"        ~: create0 ~?= [T0, T1 0, T2 0 0]
  ]

createA10 :: ADT1 t => [t Int]
createA10 = createA1 @AnyType (const []) [0]

testCreateA1 :: Test
testCreateA1 = "createA1" ~:
  [ "Identity" ~: createA10 ~?= [Identity 0]
  , "(,)"      ~: createA10 ~?= ([] :: [(String, Int)])
  , "Either"   ~: createA10 ~?= [Right 0 :: Either String Int]
  , "Maybe"    ~: createA10 ~?= [Nothing, Just 0]
  , "T"        ~: createA10 ~?= [T0, T1 0, T2 0 0]
  ]

nullaryOp0 :: (ADTRecord t, Constraints t ((~) Int)) => t
nullaryOp0 = nullaryOp @((~) Int) 0

testNullaryOp :: Test
testNullaryOp = "nullaryOp" ~:
  [ "Identity" ~: nullaryOp0 ~?= Identity 0
  , "()"       ~: nullaryOp0 ~?= ()
  , "(,)"      ~: nullaryOp0 ~?= (0, 0)
  ]

createA1'0 :: ADTRecord1 t => [t Int]
createA1'0 = createA1' @AnyType (const []) [0]

testCreateA1' :: Test
testCreateA1' = "createA1'" ~:
  [ "Identity" ~: createA1'0 ~?= [Identity 0]
  , "Pair"     ~: createA1'0 ~?= [Pair 0 0]
  ]

main :: IO Counts
main = runTestTT $ test
  [ testCreate
  , testCreateA1
  , testCreateA1'
  , testNullaryOp
  ]
