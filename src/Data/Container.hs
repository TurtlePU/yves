{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Container where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.Hashable (Hashable)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Map (Map)
import qualified Data.Map as M

infixl 9 !

class Keyed k v c | c -> k, c -> v where
  (!) :: c -> k -> v

instance Keyed Int v (IntMap v) where
  (!) = (IM.!)

instance Ord k => Keyed k v (Map k v) where
  (!) = (M.!)

instance Hashable k => Keyed k v (HashMap k v) where
  (!) = (HM.!)

-- | Class of collections which can be created from entries.
--
-- [Singleton inverse] @'singleton' i x '!' i = x@
class Keyed k v c => Singleton k v c where
  singleton :: k -> v -> c

instance Singleton Int v (IntMap v) where
  singleton = IM.singleton

instance Ord k => Singleton k v (Map k v) where
  singleton = M.singleton

instance Hashable k => Singleton k v (HashMap k v) where
  singleton = HM.singleton

type Collection k v c = (Singleton k v c, Monoid c)

infixr 6 <|

infixl 6 |>

(<|) :: Collection k v c => (k, v) -> c -> c
(i, x) <| m = singleton i x <> m

(|>) :: Collection k v c => c -> (k, v) -> c
m |> (i, x) = m <> singleton i x
