module Control.Monad.Scoped.Free where

import Control.Applicative (Applicative (..))
import Control.Monad (Monad (..))
import Control.Monad qualified as Monad
import Data.Bifoldable (Bifoldable (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Bitraversable (Bitraversable (..))
import Data.Foldable (Foldable (..))
import Data.Function (($), (.))
import Data.Functor (Functor (..), (<$>))
import Data.Maybe (Maybe)
import Data.Maybe qualified as Maybe
import Data.Traversable (Traversable (..))

data Free b v
  = FVar v
  | FTerm {fterm :: b (Free b (Maybe v)) (Free b v)}

instance (Bifunctor b) => Functor (Free b) where
  fmap f (FVar v) = FVar (f v)
  fmap f (FTerm t) = FTerm $ bimap (fmap $ fmap f) (fmap f) t

instance (Bifunctor b) => Applicative (Free b) where
  pure = FVar
  (<*>) = Monad.ap

instance (Bifunctor b) => Monad (Free b) where
  FVar v >>= f = f v
  FTerm t >>= f =
    FTerm $
      bimap
        (>>= Maybe.maybe (FVar Maybe.Nothing) (fmap Maybe.Just . f))
        (>>= f)
        t

foldrI :: (Foldable f) => (a -> b -> b) -> f a -> b -> b
foldrI f t x = foldr f x t

instance (Bifoldable b) => Foldable (Free b) where
  foldr f s (FVar v) = f v s
  foldr f s (FTerm t) = bifoldr (foldrI $ foldrI f) (foldrI f) s t

instance (Bitraversable b) => Traversable (Free b) where
  traverse f (FVar v) = FVar <$> f v
  traverse f (FTerm t) =
    FTerm <$> bitraverse (traverse $ traverse f) (traverse f) t
