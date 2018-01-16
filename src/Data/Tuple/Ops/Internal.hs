{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Tuple.Ops.Internal where

import qualified GHC.Generics as G
import GHC.Generics (Generic(..), (:*:)(..), (:+:)(..), Rec0, C1, D1, S1, M1(..), U1, K1(..))
import GHC.TypeLits
import Data.Proxy
import qualified Prelude as P 
import Prelude (Maybe(..), Int, Word, Char, Float, Double, Bool(..), ($))

-- | a sentinial datatype that represents a empty product
data End a = End

-- | Representation of tuple are shaped in a balanced tree. 
-- 'L' transforms the tree into a line, for further manipulation.
class Linearize (t :: * -> *) (b :: * -> *) where
  type L t b :: * -> *
  linearize :: t x -> b x -> L t b x

-- | base case 1. cons field with end
instance Linearize (S1 MetaS (Rec0 t)) End where
    type L (S1 MetaS (Rec0 t)) End = (S1 MetaS (Rec0 t))
    linearize a End = a

-- note that it is not possible to combine base case 2 and 3, which results in
-- a ambiguous instantiation with base case 1
--
-- | base case 2. cons field1 with field2 
instance Linearize (S1 MetaS (Rec0 t)) (S1 MetaS (Rec0 b)) where
    type L (S1 MetaS (Rec0 t)) (S1 MetaS (Rec0 b)) = S1 MetaS (Rec0 t) :*: S1 MetaS (Rec0 b)
    linearize a b = a :*: b

-- | base case 3. cons field1 with a product
instance Linearize (S1 MetaS (Rec0 t)) (b :*: c) where
    type L (S1 MetaS (Rec0 t)) (b :*: c) = S1 MetaS (Rec0 t) :*: b :*: c
    linearize a b = a :*: b

-- | inductive case. preppend a product with what ever
instance (Linearize v b, Linearize u (L v b)) => Linearize (u :*: v) b where
    type L (u :*: v) b = L u (L v b)
    linearize (a :*: b) c = linearize a (linearize b c)

-- | calculate the number of fields of a product
-- note: undefined on non-product rep
type family Length a :: Nat where
    Length (S1 MetaS (Rec0 t)) = 1
    Length (a :*: b) = Length a + Length b
length :: a x -> Proxy (Length a)
length _ = Proxy

-- | calculate the half
type family Half (a :: Nat) :: Nat where
    Half 1 = 0
    Half 2 = 1
    Half n = Half (n - 2) + 1
half :: KnownNat n => Proxy n -> Proxy (Half n)
half _ = Proxy

-- | transform the GHC's typelit into SNat
-- We rely on the SNat to define Take and Drop
data SNat = One | Succ SNat
type family ToSNat (a :: Nat) :: SNat where
    ToSNat 1 = One
    ToSNat n = Succ (ToSNat (n - 1))
tosnat :: KnownNat n => Proxy n -> Proxy (ToSNat n)
tosnat _ = Proxy

-- | take the first n elements from a product
class Take (n :: SNat) (a :: * -> *) where
    type T n a :: * -> *
    take :: Proxy n -> a x -> T n a x

-- | base case 1. take one out of singleton
instance Take One (S1 MetaS (Rec0 t)) where
    type T One (S1 MetaS (Rec0 t)) = S1 MetaS (Rec0 t)
    take _ a = a

-- | base case 2. take one out of a product
instance Take One (a :*: b) where
    type T One (a :*: b) = a
    take _ (a :*: _) = a

-- | inductive case. take (n+1) elements
instance Take n b => Take (Succ n) (a :*: b) where
    type T (Succ n) (a :*: b) = a :*: T n b
    take (_ :: Proxy (Succ n)) (a :*: b) = a :*: take (Proxy :: Proxy n) b

-- | drop the first n elements from a product
class Drop (n :: SNat) (a :: * -> *) where
    type D n a :: * -> *
    drop :: Proxy n -> a x -> D n a x

-- | base case 1. drop one from product
instance Drop One (a :*: b) where
    type D One (a :*: b) = b
    drop _ (_ :*: b) = b

-- | inductive case. drop (n+1) elements
instance Drop n b => Drop (Succ n) (a :*: b) where
    type D (Succ n) (a :*: b) = D n b
    drop (_ :: Proxy (Succ n)) (a :*: b) = drop (Proxy :: Proxy n) b

-- | 'Normalize' converts a linear product back into a balanced tree.
class Normalize (a :: * -> *) where
    type N a :: * -> * 
    normalize :: a x -> N a x

-- | base case 1. singleton
instance Normalize (S1 MetaS (Rec0 t)) where
    type N (S1 MetaS (Rec0 t)) = S1 MetaS (Rec0 t)
    normalize a = a

-- | inductive case. product
instance (KnownNat (Length a + Length b),
          KnownNat (Half (Length a + Length b)),
          Take (ToSNat (Half (Length a + Length b))) (a :*: b),
          Drop (ToSNat (Half (Length a + Length b))) (a :*: b),
          Normalize ((T (ToSNat (Half (Length a + Length b))) (a :*: b))), 
          Normalize ((D (ToSNat (Half (Length a + Length b))) (a :*: b)))) 
    => Normalize (a :*: b) where
    type N (a :*: b) = N (T (ToSNat (Half (Length a + Length b))) (a :*: b)) :*: 
                       N (D (ToSNat (Half (Length a + Length b))) (a :*: b))
    normalize v = let n1 = length v :: Proxy (Length a + Length b)
                      n2 = tosnat $ half n1
                  in normalize (take n2 v) :*: normalize (drop n2 v)

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
