{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Tuple.Ops(
    module Data.Tuple.Ops.Uncons
) where

import GHC.Generics
import Data.Tuple.Ops.Uncons

deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char
deriving instance Generic Float
deriving instance Generic Double
deriving instance Generic (a,b,c,d,e,f,g,h)
deriving instance Generic (a,b,c,d,e,f,g,h,i)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k,l)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k,l,m)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k,l,m,n)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o)
deriving instance Generic (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p)