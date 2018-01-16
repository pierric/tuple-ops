------------------------------------------------------------
-- |
-- Module      :  Data.Tuple.Ops
-- Description :  various operations on n-ary tuples via GHC.Generics
-- Copyright   :  (c) 2018 Jiasen Wu
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Jiasen Wu <jiasenwu@hotmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
--
-- This module exports various operations on n-ary tuples
------------------------------------------------------------
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