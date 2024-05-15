{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Container where

import Control.Composition ((.*))
import qualified Data.HashMap.Lazy as HML
import qualified Data.HashMap.Monoidal as MHM
import Data.Hashable (Hashable)
import qualified Data.IntMap as IM
import qualified Data.IntMap.Monoidal as MIM
import qualified Data.Map as M
import qualified Data.Map.Monoidal as MM
import Data.Monoid (First (..))

infixl 9 !?

-- | Class of indexed structures.
--
-- [Index is semigroup hom] @(c '<>' d) '!?' k = c '!?' k '<>' d '!?' k@
-- [Index is monoid hom] @'mempty' '!?' k = 'mempty'@
class Indexed k v c | c k -> v where
  (!?) :: c -> k -> v

instance Indexed Int (First v) (IM.IntMap v) where
  (!?) = First .* (IM.!?)

instance Ord k => Indexed k (First v) (M.Map k v) where
  (!?) = First .* (M.!?)

instance Hashable k => Indexed k (First v) (HML.HashMap k v) where
  (!?) = First .* (HML.!?)

instance Indexed Int (Maybe v) (MIM.MonoidalIntMap v) where
  (!?) = flip MIM.lookup

instance Ord k => Indexed k (Maybe v) (MM.MonoidalMap k v) where
  (!?) = flip MM.lookup

instance Hashable k => Indexed k (Maybe v) (MHM.MonoidalHashMap k v) where
  (!?) = flip MHM.lookup

-- | Class of collections which can be created from entries.
--
-- [Singleton inverse] @'singleton' i x '!?' i = x@
class Indexed k v c => Singleton k v c where
  singleton :: k -> v -> c

firstSingle :: Monoid c => (k -> v -> c) -> k -> First v -> c
firstSingle singleton k (First (Just v)) = singleton k v
firstSingle _ _ _ = mempty

instance Singleton Int (First v) (IM.IntMap v) where
  singleton = firstSingle IM.singleton

instance Ord k => Singleton k (First v) (M.Map k v) where
  singleton = firstSingle M.singleton

instance Hashable k => Singleton k (First v) (HML.HashMap k v) where
  singleton = firstSingle HML.singleton

instance Singleton Int (Maybe v) (MIM.MonoidalIntMap v) where
  singleton = maybe MIM.empty . MIM.singleton

instance Ord k => Singleton k (Maybe v) (MM.MonoidalMap k v) where
  singleton = maybe MM.empty . MM.singleton

instance Hashable k => Singleton k (Maybe v) (MHM.MonoidalHashMap k v) where
  singleton = maybe (MHM.MonoidalHashMap mempty) . MHM.singleton

infixr 6 <|

infixl 6 |>

(<|) :: (Semigroup c, Singleton k v c) => (k, v) -> c -> c
(i, x) <| m = singleton i x <> m

(|>) :: (Semigroup c, Singleton k v c) => c -> (k, v) -> c
m |> (i, x) = m <> singleton i x
