{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Core where

import Control.Applicative (liftA2)
import Control.Lens (Field1, Getting, makePrisms, over, (^?), _1)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, asks, local)
import Data.Functor.Foldable (cata, embed)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Monoid (First)

infixl 1 :$:

infixr 0 :->:

infixr 1 :.:

data Term
  = Type Int
  | Var Int
  | Type :->: Type
  | Type :.: Term
  | Term :$: Term
  deriving (Eq)

type Type = Term

makeBaseFunctor ''Term
makePrisms ''Term

data TypeError = EType | EArrow | EEqual

infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
infer = \case
  Type i -> return $ Type (i + 1)
  Var x -> asks (!! x)
  t :->: u -> do
    i <- infer t >>= level
    j <- local (t :) (infer u) >>= level
    return $ Type (i `max` j)
  t :.: b -> do
    infer t >>= level
    (t :->:) <$> local (t :) (infer b)
  f :$: x -> do
    (tx, ty) <- infer f >>= domains
    check x tx
    return (ty // x)
  where
    level :: MonadError TypeError m => Term -> m Int
    level = tries _Type EType

    domains :: MonadError TypeError m => Term -> m (Term, Term)
    domains = tries (.:->:) EArrow

    tries :: MonadError e m => Getting (First a) s a -> e -> s -> m a
    tries pr err = maybe (throwError err) return . (^? pr)

check :: (MonadReader [Term] m, MonadError TypeError m) => Term -> Type -> m ()
check e t = do
  t' <- infer e
  if normalForm t == normalForm t'
    then return ()
    else throwError EEqual

normalForm :: Term -> Term
normalForm = cata $ \case
  (_ :.: b) :$:$ x -> normalForm (b // x)
  other -> embed other

(//) :: Term -> Term -> Term
t // e = shift (sub t (0, shift e (0, 1))) (1, -1)
  where
    up :: (Field1 s s a a, Enum a, MonadReader s m) => m b -> m b
    up = local (over _1 succ)

    sub :: Term -> (Int, Term) -> Term
    sub = cata $ \case
      VarF y -> \(x, v) -> if x == y then v else Var y
      t :->:$ u -> liftA2 (:->:) t (up u)
      t :.:$ b -> liftA2 (:.:) t (up b)
      other -> embed <$> sequence other

    shift :: Term -> (Int, Int) -> Term
    shift = cata $ \case
      VarF y -> Var <$> \(b, d) -> if y >= b then y + d else y
      t :->:$ u -> liftA2 (:->:) t (up u)
      t :.:$ b -> liftA2 (:.:) t (up b)
      other -> embed <$> sequence other
