{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Core where

import Control.Applicative (liftA2)
import Control.Lens (ASetter', Getting, makePrisms, over, (^?), _1)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, asks, local)
import Data.Function (on)
import Data.Monoid (First)

tries :: MonadError e m => Getting (First a) s a -> e -> m s -> m a
tries pr err x = x >>= maybe (throwError err) return . (^? pr)

locals :: MonadReader s m => ASetter' s a -> (a -> a) -> m b -> m b
locals s = local . over s

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

makePrisms ''Term

data TypeError = EType | EArrow | EEqual

infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
infer (Type i) = return $ Type (i + 1)
infer (Var x) = asks (!! x)
infer (t :->: u) = do
  i <- tries _Type EType (infer t)
  j <- tries _Type EType $ local (t :) (infer u)
  return $ Type (i `max` j)
infer (t :.: b) = do
  tries _Type EType (infer t)
  (t :->:) <$> local (t :) (infer b)
infer (f :$: x) = do
  (tx, ty) <- tries (.:->:) EArrow (infer f)
  check x tx
  return (ty // x)

check :: (MonadReader [Term] m, MonadError TypeError m) => Term -> Term -> m ()
check e t = do
  t' <- infer e
  if ((==) `on` normalForm) t t'
    then return ()
    else throwError EEqual

normalForm :: Term -> Term
normalForm (Type i) = Type i
normalForm (Var x) = Var x
normalForm (t :->: u) = normalForm t :->: normalForm u
normalForm (t :.: b) = normalForm t :.: normalForm b
normalForm (f :$: x) = case normalForm f of
  _ :.: b -> normalForm (b // normalForm x)
  f' -> f' :$: normalForm x

(//) :: Term -> Term -> Term
t // e = shift (sub t (0, shift e (0, 1))) (1, -1)
  where
    sub :: Term -> (Int, Term) -> Term
    sub (Type i) = const (Type i)
    sub (Var y) = \(x, v) -> if x == y then v else Var y
    sub (t :->: u) = liftA2 (:->:) (sub t) (locals _1 succ $ sub u)
    sub (t :.: b) = liftA2 (:.:) (sub t) (locals _1 succ $ sub b)
    sub (f :$: b) = liftA2 (:$:) (sub f) (sub b)

    shift :: Term -> (Int, Int) -> Term
    shift (Type i) = const (Type i)
    shift (Var y) = Var <$> \(b, d) -> if y >= b then y + d else y
    shift (t :->: u) = liftA2 (:->:) (shift t) (locals _1 succ $ shift u)
    shift (t :.: u) = liftA2 (:.:) (shift t) (locals _1 succ $ shift u)
    shift (f :$: x) = liftA2 (:$:) (shift f) (shift x)
