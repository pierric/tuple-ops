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
-- This module define 'uncons'. Examples are given below:
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
------------------------------------------------------------
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Tuple.Ops.Uncons (uncons, Uncons, Unconsable) where

import           Data.Proxy
import           Data.Tuple.Ops.Internal
import           GHC.Generics            ((:*:) (..), (:+:) (..), C1, D1,
                                          FixityI (..), Generic (..), K1 (..),
                                          M1 (..), Meta (..), Rec0, S1, U1,
                                          URec)
import           GHC.TypeLits            (Symbol)
import           RIO                     hiding (to)
import           Type.Family.Nat         (N1)

-- | 'HeadR' is a type function that takes the first element of a tuple
type family HeadR (f :: * -> *) :: * -> * where
    HeadR (C1 mc (S1 ms (URec a))) = C1 mc (S1 ms (URec a))     -- unlifted type
    HeadR (C1 mc (S1 ms (Rec0 a))) = C1 mc (S1 ms (Rec0 a))     -- lifted type
    HeadR (a :+: b) = a :+: b
    HeadR (RepOfTuple "(,)" (S1 MetaS (Rec0 a) :*: S1 MetaS (Rec0 b))) = UnD1 (Rep a)
    HeadR (RepOfTuple tcon  (a :*: b :*: c)) = UnD1 (Rep (UnRec0 (UnS1 (N (T N1 (L (a :*: b :*: c)))))))
-- | 'TailR' is a type function that drops the first element of a tuple
type family TailR (f :: * -> *) :: * -> * where
    TailR (C1 mc (S1 ms (URec a))) = C1 ('MetaCons "()" 'PrefixI 'False) U1 -- unlifted type
    TailR (C1 mc (S1 ms (Rec0 a))) = C1 ('MetaCons "()" 'PrefixI 'False) U1 -- lifted type
    TailR (a :+: b) = C1 ('MetaCons "()" 'PrefixI 'False) U1
    TailR (RepOfTuple "(,)" (S1 MetaS (Rec0 a) :*: S1 MetaS (Rec0 b))) = UnD1 (Rep b)
    TailR (RepOfTuple tcon  (a :*: b :*: c)) = RepOfTuple (TupleConPred tcon) (N (D N1 (L (a :*: b :*: c))))

-- | Abstract type class for generic representation of a /uncons/able datatype
class UnconsableR f where
    unconsR :: f a -> (HeadR f a, TailR f a)

-- | primitive datatype
-- 'HeadR' is the datatype itself
-- 'TailR' is ()
instance UnconsableR (C1 mc (S1 ms (URec a))) where
    unconsR a = (a, unM1 (from ()))

-- | lifted datatype
-- 'HeadR' is the datatype itself
-- 'TailR' is ()
instance UnconsableR (C1 mc (S1 ms (Rec0 a))) where
    unconsR a = (a, unM1 (from ()))

-- | sum datatype
-- 'HeadR' is the datatype itself
-- 'TailR' is ()
instance UnconsableR (a :+: b) where
    unconsR a = (a, unM1 (from ()))

-- | pair
-- 'HeadR' is the first element
-- 'TailR' is the second element
instance (Generic t1, Rep t1 ~ D1 mt1 ct1,
          Generic t2, Rep t2 ~ D1 mt2 ct2)
    => UnconsableR (RepOfTuple "(,)" (S1 MetaS (Rec0 t1) :*: S1 MetaS (Rec0 t2))) where
    unconsR (M1 (a :*: b)) = (unM1 $ from $ unK1 $ unM1 a, unM1 $ from $ unK1 $ unM1 b)

-- | tuple of arity > 2
-- 'HeadR' is the first element
-- 'TailR' is the rest all elements
instance (Linearize (a :*: b :*: c), L (a :*: b :*: c) ~ (S1 MetaS (Rec0 t) : w),
          Generic t, Rep t ~ D1 hm hc, Normalize w)
    => UnconsableR (RepOfTuple tcon (a :*: b :*: c)) where
    unconsR a = let tup = linearize (unM1 a)
                    one = Proxy :: Proxy N1
                    h = unM1 $ from $ unK1 $ unM1 $ normalize $ take' one tup
                    t = M1 $ normalize $ drop' one tup
                in (h, t)

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

-- | A constraint on any 'uncons'able data type, where
-- @a@ is the input type, and @(b,c)@ is the output type
type Unconsable a b c = (Generic a, Generic b, Generic c, Uncons a ~ (b, c),
                         Rep a ~ D1 (MetaOfD1 (Rep a)) (UnD1 (Rep a)),
                         Rep b ~ D1 (MetaOfD1 (Rep b)) (UnD1 (Rep b)),
                         Rep c ~ D1 (MetaOfD1 (Rep c)) (UnD1 (Rep c)),
                         UnconsableR (UnD1 (Rep a)),
                         HeadR (UnD1 (Rep a)) ~ (UnD1 (Rep b)),
                         TailR (UnD1 (Rep a)) ~ (UnD1 (Rep c)))

-- | 'uncons' takes primitive, pair, tuple,
-- and produces a pair of its first data and the rest elements.
uncons :: Unconsable a b c => a -> (b, c)
uncons x = let (a, b) = unconsR $ unM1 $ from x in (to $ M1 a, to $ M1 b)
