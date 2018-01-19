------------------------------------------------------------
-- |
-- Module      :  Data.Tuple.Ops.Internal
-- Description :  various operations on n-ary tuples via GHC.Generics
-- Copyright   :  (c) 2018 Jiasen Wu
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Jiasen Wu <jiasenwu@hotmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
--
-- This module defins operations to manipulate the generic 
-- representation of tuple.
------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
module Data.Tuple.Ops.Internal where

import qualified GHC.Generics as G
import GHC.Generics (Generic(..), (:*:)(..), (:+:)(..), Rec0, C1, D1, S1, M1(..), U1, K1(..))
import Data.Proxy
import Data.Type.Combinator
import Data.Type.Product
import Type.Family.List
import Type.Class.Witness
import qualified Type.Family.Nat as Nat
import qualified Prelude as P 
import Prelude (Maybe(..), Int, Word, Char, Float, Double, Bool(..), ($), (.))

newtype TupleR (f :: [* -> *]) x = TupleR { unTupleR :: Tuple (f <&> x)}

-- class X' (t :: * -> *) where
--     type X t :: [* -> *]
--     foo :: t x -> TupleR (X t) x
  
-- instance X' v => X' (u :*: v) where
--     type X (u :*: v) = u : X v
--     foo (a :*: b) = TupleR $ I a :< (unTupleR $ foo b)

aaa :: Wit (((a :< b) ++ c) ~ (a :< (b ++ c)))
aaa = Wit
bbb :: Wit (((a :< b) <&> x) ~ ((a x) :< (b <&> x)))
bbb = Wit
class MyWit (a :: [* -> *]) where
    ccc :: Wit (((a ++ b) <&> x) ~ ((a <&> x) ++ (b <&> x)))
instance MyWit '[] where
    ccc = Wit
instance MyWit (a :< as) where
    ccc = Wit

-- | Representation of tuple are shaped in a balanced tree. 
-- 'L' transforms the tree into a list, for further manipulation.
class Linearize (t :: * -> *) where
  type L t :: [* -> *]
  linearize :: t x -> TupleR (L t) x

-- | base case. sinleton
instance Linearize (S1 MetaS (Rec0 t)) where
    type L (S1 MetaS (Rec0 t)) = '[S1 MetaS (Rec0 t)]
    linearize = TupleR . only . I

-- | inductive case. preppend a product with what ever
instance (Linearize v, Linearize u) => Linearize (u :*: v) where
    type L (u :*: v) = L u ++ L v
    linearize (a :*: b) = TupleR $ append' (unTupleR $ linearize a) (unTupleR $ linearize b)

length' :: TupleR a x -> Proxy (Nat.Len a)
length' _ = Proxy

-- | calculate the half
type family Half (a :: Nat.N) :: Nat.N where
    Half (Nat.S Nat.Z) = Nat.Z
    Half (Nat.S (Nat.S Nat.Z)) = Nat.S Nat.Z
    Half (Nat.S (Nat.S n)) = Nat.S (Half n)
-- | calculate the half
half :: Proxy n -> Proxy (Half n)
half _ = Proxy

-- | take the first n elements from a product
class Take (n :: Nat.N) (a :: [* -> *]) where
    type T n a :: [* -> *]
    take :: Proxy n -> TupleR a x -> TupleR (T n a) x

-- | base case. take one out of singleton
instance Take Nat.Z xs where
    type T Nat.Z xs = xs
    take _ a = a

-- | inductive case. take (n+1) elements
instance Take n xs => Take (Nat.S n) (x : xs) where
    type T (Nat.S n) (x : xs) = x : T n xs
    take (_ :: Proxy (Nat.S n)) (TupleR (a :< as)) = TupleR (a :< unTupleR (take (Proxy :: Proxy n) (TupleR as)))

-- | drop the first n elements from a product
class Drop (n :: Nat.N) (a :: [* -> *]) where
    type D n a :: [* -> *]
    drop :: Proxy n -> TupleR a x -> TupleR (D n a) x

-- | base case. drop one from product
instance Drop Nat.Z as where
    type D Nat.Z as = as
    drop _ a = a

-- | inductive case. drop (n+1) elements
instance Drop n as => Drop (Nat.S n) (a : as) where
    type D (Nat.S n) (a : as) = D n as
    drop (_ :: Proxy (Nat.S n)) (TupleR (a :< as)) = drop (Proxy :: Proxy n) (TupleR as)

-- | 'Normalize' converts a linear product back into a balanced tree.
class Normalize (a :: [* -> *]) where
    type N a :: * -> *
    normalize :: TupleR a x -> N a x

-- | base case. singleton
instance Normalize '[S1 MetaS (Rec0 t)] where
    type N '[S1 MetaS (Rec0 t)] = S1 MetaS (Rec0 t)
    normalize a = getI $ head' $ unTupleR a

-- | inductive case. product
instance (Take (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c),
          Drop (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c),
          Normalize (T (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c)), 
          Normalize (D (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c))) 
    => Normalize (a :< b :< c) where
    type N (a :< b :< c) = N (T (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c)) :*: 
                           N (D (Half (Nat.N2 Nat.+ Nat.Len c)) (a :< b :< c))
    normalize v = let n = half (length' v)
                  in normalize (take n v) :*: normalize (drop n v)

type MetaS = 'G.MetaSel 'Nothing 'G.NoSourceUnpackedness 'G.NoSourceStrictness 'G.DecidedLazy
-- | utility type function to trim the Rec0 
type family UnRec0 t where
    UnRec0 (Rec0 t) = t
-- | utility type function to trim the S1
type family UnS1 t where
    UnS1 (S1 _ t) = t
-- | utility type function to trim the D1
type family UnD1 t where
    UnD1 (D1 _ t) = t
