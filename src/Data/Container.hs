{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Container where

infixl 9 !

class Keyed c k v | c -> k, c -> v where
  (!) :: c -> k -> v

-- | Class of collections which can be created from entries.
--
-- [Singleton inverse] @'singleton' i x '!' i = x@
class Keyed c k v => Singleton c k v where
  singleton :: k -> v -> c

type Collection c k v = (Singleton c k v, Monoid c)
