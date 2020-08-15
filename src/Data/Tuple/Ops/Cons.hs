------------------------------------------------------------
-- |
-- Module      :  Data.Tuple.Ops.Cons
-- Description :  various operations on n-ary tuples via GHC.Generics
-- Copyright   :  (c) 2018 Jiasen Wu
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Jiasen Wu <jiasenwu@hotmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
--
-- This module define 'cons'. Examples are given below:
--
-- >>> cons (1::Int) ()
-- 1
--
-- >>> cons (1::Int) 'a'
-- (1,'a')
--
-- >>> cons (True,'a') "S"
-- ((True,'a'),"S")
--
-- >>> cons "S" (True,'a')
-- ("S",True,'a')
--
------------------------------------------------------------
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Tuple.Ops.Cons (cons, Cons, Consable) where

import           Data.Tuple.Ops.Internal
import           GHC.Generics            ((:*:) (..), (:+:) (..), C1, D1,
                                          Generic (..), K1 (..), M1 (..), Rec0,
                                          S1, U1, URec)
import           GHC.TypeLits            (Symbol)
import           RIO                     hiding (to)
import           Type.Family.List

-- | Abstract type class for generic representation of a /cons/able datatype
class ConsableR va rb where
    -- | @consR@ takes a value of type @va@ and a value of type @vb@ together @vb@'s representation,
    -- returns the cons'ed value. Note that, 'ConsableR' is inductively scrutinize @vb@'s
    -- representation, however this representation is only a dummy argument, since the result is
    -- constructed from the value directly.
    consR :: (Generic vb, Rep vb ~ D1 (MetaOfD1 (Rep vb)) rb) => va -> vb -> rb x -> ConsR va rb vb x

-- | Type function to calculate the type of cons'ed value
type family ConsR va rb vb where
    ConsR va (C1 mc U1) vb = UnD1 (Rep va)
    ConsR va (C1 mc (S1 ms (URec b))) vb = RepOfTuple "(,)" (S1 MetaS (Rec0 va) :*: S1 MetaS (Rec0 vb))
    ConsR va (C1 mc (S1 ms (Rec0 b))) vb = RepOfTuple "(,)" (S1 MetaS (Rec0 va) :*: S1 MetaS (Rec0 vb))
    ConsR va (b0 :+: b1) vb = RepOfTuple "(,)" (S1 MetaS (Rec0 va) :*: S1 MetaS (Rec0 vb))
    ConsR va (RepOfTuple tcon (b0 :*: b1)) vb = RepOfTuple (TupleConSucc tcon) (N (L (S1 MetaS (Rec0 va) :*: b0 :*: b1)))

instance (Generic a, Rep a ~ D1 (MetaOfD1 (Rep a)) (UnD1 (Rep a))) => ConsableR a (C1 mc U1) where
    consR a _ _ = unM1 $ from a

instance ConsableR va (C1 mc (S1 ms (URec b))) where
    consR a b _ = M1 (M1 (K1 a) :*: M1 (K1 b))

instance ConsableR va (C1 mc (S1 ms (Rec0 b))) where
    consR a b _ = M1 (M1 (K1 a) :*: M1 (K1 b))

instance ConsableR va (b0 :+: b1) where
    consR a b _ = M1 (M1 (K1 a) :*: M1 (K1 b))

instance (Linearize b0, Linearize b1,
          Normalize ((S1 MetaS (Rec0 va) :< L b0 ++ L b1)),
          AppDistributive (L b0)) => ConsableR va (RepOfTuple tcon (b0 :*: b1)) where
    consR a b _ = M1 $ normalize $ linearize $ (M1 (K1 a) :: S1 MetaS (Rec0 va) x) :*: unM1 (unM1 (from b))

-- | calculate the tuple constructor of the size 1 bigger
-- upto the tupel of arity of 15
type family TupleConSucc (a :: Symbol) where
    TupleConSucc "(,)" = "(,,)"
    TupleConSucc "(,,)" = "(,,,)"
    TupleConSucc "(,,,)" = "(,,,,)"
    TupleConSucc "(,,,,)" = "(,,,,,)"
    TupleConSucc "(,,,,,)" = "(,,,,,,)"
    TupleConSucc "(,,,,,,)" = "(,,,,,,,)"
    TupleConSucc "(,,,,,,,)" = "(,,,,,,,,)"
    TupleConSucc "(,,,,,,,,)" = "(,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,)" = "(,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,)" = "(,,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,,)" = "(,,,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,,,)"
    TupleConSucc "(,,,,,,,,,,,,,,,)" = "(,,,,,,,,,,,,,,,,)"

-- | calculate the result type of 'cons'
type family Cons a b where
    Cons z (a,b) = (z,a,b)
    Cons z (a,b,c) = (z,a,b,c)
    Cons z (a,b,c,d) = (z,a,b,c,d)
    Cons z (a,b,c,d,e) = (z,a,b,c,d,e)
    Cons z (a,b,c,d,e,f) = (z,a,b,c,d,e,f)
    Cons z (a,b,c,d,e,f,g) = (z,a,b,c,d,e,f,g)
    Cons z (a,b,c,d,e,f,g,h) = (z,a,b,c,d,e,f,g,h)
    Cons z (a,b,c,d,e,f,g,h,i) = (z,a,b,c,d,e,f,g,h,i)
    Cons z (a,b,c,d,e,f,g,h,i,j) = (z,a,b,c,d,e,f,g,h,i,j)
    Cons z (a,b,c,d,e,f,g,h,i,j,k) = (z,a,b,c,d,e,f,g,h,i,j,k)
    Cons z (a,b,c,d,e,f,g,h,i,j,k,l) = (z,a,b,c,d,e,f,g,h,i,j,k,l)
    Cons z (a,b,c,d,e,f,g,h,i,j,k,l,m) = (z,a,b,c,d,e,f,g,h,i,j,k,l,m)
    Cons z (a,b,c,d,e,f,g,h,i,j,k,l,m,n) = (z,a,b,c,d,e,f,g,h,i,j,k,l,m,n)
    Cons z (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) = (z,a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
    Cons z () = z
    Cons z a  = (z,a)

-- | A constraint on any 'cons'able data type, where
-- @a@ and @b@ are the input, and @c@ is the output.
type Consable a b c = (Generic a, Generic b, Generic c, Cons a b ~ c,
                       Rep b ~ D1 (MetaOfD1 (Rep b)) (UnD1 (Rep b)),
                       Rep c ~ D1 (MetaOfD1 (Rep c)) (UnD1 (Rep c)),
                       ConsableR a (UnD1 (Rep b)),
                       ConsR a (UnD1 (Rep b)) b ~ (UnD1 (Rep c)))

-- | 'cons' takes two datatype, and produces a tuple of them.
-- if @b@ is unit, then @a@ is returned.
-- if @b@ is not a tuple, then a pair of @(a,b)@ is returned.
-- otherwise, @a@ is placed in front of @b@.
cons :: Consable a b c => a -> b -> c
cons a b = to $ M1 $ consR a b (unM1 $ from b)
