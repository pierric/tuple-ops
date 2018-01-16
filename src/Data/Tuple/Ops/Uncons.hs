------------------------------------------------------------
-- |
-- Module      :  Data.Tuple.Ops.Uncons
-- Description :  various operations on n-ary tuples via GHC.Generics
-- Copyright   :  (c) 2018 Jiasen Wu
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Jiasen Wu <jiasenwu@hotmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
--
-- This module define 'uncons'
------------------------------------------------------------
{-# LANGUAGE TypeSynonymInstances #-}

-- | Examples are given below:
--
-- >>> uncons (1::Int)
-- (1,())
--
-- >>> uncons (1::Int,'a')
-- (1,'a')
--
-- >>> uncons (True,'a', "S")
-- (True,('a',"S"))
-- 

module Data.Tuple.Ops.Uncons (uncons) where

import qualified GHC.Generics as G
import GHC.Generics (Generic(..), (:*:)(..), (:+:)(..), Rec0, C1, D1, S1, M1(..), U1, K1(..))
import GHC.TypeLits
import Data.Tuple.Ops.Internal

-- | representation of a pair
type RepOfPair t1 t2 = C1 ('G.MetaCons "(,)" 'G.PrefixI 'False) (S1 MetaS (Rec0 t1) :*: S1 MetaS (Rec0 t2))
-- | representation of a tuple of arity > 2, in which @/u/@ is of the form @_ :*: _@
type RepOfTuple c u = C1 ('G.MetaCons c 'G.PrefixI 'False) u 

-- | 'HeadR' is a type function that takes the first element of a tuple
type family HeadR (f :: * -> *) :: * -> * where
    HeadR (C1 mc (S1 ms (G.URec a))) = C1 mc (S1 ms (G.URec a))
    HeadR (a :+: b) = a :+: b
    HeadR (RepOfPair t1 t2) = UnD1 (Rep t1)
    HeadR (RepOfTuple tcon (a :*: b :*: c)) = UnD1 (Rep (UnRec0 (UnS1 (T One (L (a :*: b :*: c) End)))))
-- | 'TailR' is a type function that drops the first element of a tuple
type family TailR (f :: * -> *) :: * -> * where
    TailR (C1 mc (S1 ms (G.URec a))) = C1 ('G.MetaCons "()" 'G.PrefixI 'False) U1
    TailR (a :+: b) = C1 ('G.MetaCons "()" 'G.PrefixI 'False) U1
    TailR (RepOfPair t1 t2) = UnD1 (Rep t2)
    TailR (RepOfTuple tcon (a :*: b :*: c)) = RepOfTuple (TupleConPred tcon) (N (D One (L (a :*: b :*: c) End)))

-- | Abstract type class for generic representation of a /uncons/able datatype
class UnconsR f where
    unconsR :: f a -> (HeadR f a, TailR f a)

-- | primitive datatype
-- 'HeadR' is the datatype itself
-- 'TailR' is ()
instance UnconsR (C1 mc (S1 ms (G.URec a))) where
    unconsR a = (a, unM1 (from ()))

-- | sum datatype
-- 'HeadR' is the datatype itself
-- 'TailR' is ()
instance UnconsR (a :+: b) where
    unconsR a = (a, unM1 (from ()))

-- | pair
-- 'HeadR' is the first element
-- 'TailR' is the second element
instance (Generic t1, Rep t1 ~ D1 mt1 ct1,
          Generic t2, Rep t2 ~ D1 mt2 ct2)
    => UnconsR (RepOfPair t1 t2) where
    unconsR (M1 (a :*: b)) = (unM1 $ from $ unK1 $ unM1 a, unM1 $ from $ unK1 $ unM1 b)

-- | tuple of arity > 2
-- 'HeadR' is the first element
-- 'TailR' is the rest all elements
instance (Linearize c End, Linearize b (L c End), Linearize a (L b (L c End)),
          L a (L b (L c End)) ~ (S1 MetaS (Rec0 t) :*: w), 
          Generic t, Rep t ~ D1 hm hc, Normalize w) 
    => UnconsR (RepOfTuple tcon (a :*: b :*: c)) where
    unconsR a = case linearize (unM1 a) End of
                  u :*: v -> (unM1 $ from $ unK1 $ unM1 u, M1 $ normalize v)

-- | calculate the tuple constructor of the size 1 smaller
-- upto the tupel of arity of 16
type family TupleConPred (a :: Symbol) where
    TupleConPred "(,,)" = "(,)"
    TupleConPred "(,,,)" = "(,,)"
    TupleConPred "(,,,,)" = "(,,,)"
    TupleConPred "(,,,,,)" = "(,,,,)"
    TupleConPred "(,,,,,,)" = "(,,,,,)"
    TupleConPred "(,,,,,,,)" = "(,,,,,,)"
    TupleConPred "(,,,,,,,,)" = "(,,,,,,,)"
    TupleConPred "(,,,,,,,,,)" = "(,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,)" = "(,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,)" = "(,,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,,)" = "(,,,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,,)"
    TupleConPred "(,,,,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,,,)"

-- | calculate the result type of 'uncons'
type family Uncons a where
    Uncons (a,b) = (a,b)
    Uncons (a,b,c) = (a, (b,c))
    Uncons (a,b,c,d) = (a, (b,c,d))
    Uncons (a,b,c,d,e) = (a, (b,c,d,e))
    Uncons (a,b,c,d,e,f) = (a, (b,c,d,e,f))
    Uncons (a,b,c,d,e,f,g) = (a, (b,c,d,e,f,g))
    Uncons (a,b,c,d,e,f,g,h) = (a, (b,c,d,e,f,g,h))
    Uncons (a,b,c,d,e,f,g,h,i) = (a, (b,c,d,e,f,g,h,i))
    Uncons (a,b,c,d,e,f,g,h,i,j) = (a, (b,c,d,e,f,g,h,i,j))
    Uncons (a,b,c,d,e,f,g,h,i,j,k) = (a, (b,c,d,e,f,g,h,i,j,k))
    Uncons (a,b,c,d,e,f,g,h,i,j,k,l) = (a, (b,c,d,e,f,g,h,i,j,k,l))
    Uncons (a,b,c,d,e,f,g,h,i,j,k,l,m) = (a, (b,c,d,e,f,g,h,i,j,k,l,m))
    Uncons (a,b,c,d,e,f,g,h,i,j,k,l,m,n) = (a, (b,c,d,e,f,g,h,i,j,k,l,m,n))
    Uncons (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = (a, (b,c,d,e,f,g,h,i,j,k,l,m,n,o))
    Uncons (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) = (a, (b,c,d,e,f,g,h,i,j,k,l,m,n,o,p))
    Uncons a = (a, ())

-- | 'uncons' takes primitive, pair, tuple
-- and produces a pair of its first data and the rest elements.
uncons :: (Generic a, Rep a ~ D1 ma ra, Uncons a ~ (b, c),
           Generic b, Rep b ~ D1 mb rb,
           Generic c, Rep c ~ D1 mc rc,
           UnconsR ra, HeadR ra ~ rb, TailR ra ~ rc)
       => a -> Uncons a 
uncons x = let (a, b) = unconsR $ unM1 $ from x in (to $ M1 a, to $ M1 b)