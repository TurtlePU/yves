{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Collection where

import Data.Kind (Type)
import Data.Maybe (Maybe)
import Data.Monoid (Monoid, (<>))
import Data.Traversable (Traversable)

class (forall v. Monoid (f v), Traversable f) => Collection f where
  type Key f :: Type

  singleton :: Key f -> v -> f v
  (?!) :: f v -> Key f -> Maybe v

insert :: (Collection f) => Key f -> v -> f v -> f v
insert k v = (singleton k v <>)
