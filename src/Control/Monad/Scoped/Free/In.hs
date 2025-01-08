{-# LANGUAGE DeriveFunctor #-}

module Control.Monad.Scoped.Free.In where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Data.Either (Either)
import Data.Either qualified as Either
import Data.Eq (Eq)
import Data.Foldable (Foldable (..))
import Data.Function ((.))
import Data.Functor (Functor (..))
import Data.Maybe (Maybe)
import Data.Maybe qualified as Maybe
import Data.Traversable (Traversable (..))

data In v = Here | There v deriving (Eq, Functor)

elim :: d -> (v -> d) -> In v -> d
elim d _ Here = d
elim _ f (There v) = f v

toMaybe :: In v -> Maybe v
toMaybe = elim Maybe.Nothing Maybe.Just

ein :: Either l (In r) -> In (Either l r)
ein = Either.either (There . Either.Left) (fmap Either.Right)

ien :: In (Either l r) -> Either l (In r)
ien = elim (Either.Right Here) (fmap There)

instance Applicative In where
  pure = There
  (<*>) = Monad.ap

instance Monad In where
  (>>=) i f = elim Here f i

instance Foldable In where
  foldr f s = elim s (`f` s)

instance Traversable In where
  traverse f = elim (pure Here) (fmap There . f)
