{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Yves.YTerm where

import Control.Monad.Scoped.Free (Free)
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In)
import Control.Monad.Scoped.Free.In qualified as In
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Sum qualified as Sum
import Data.Bool (Bool)
import Data.Either (Either)
import Data.Either qualified as Either
import Data.Function (($), (.))
import Data.Functor (Functor (..))
import Yves.Core.Level (Level)
import Yves.Core.TermF qualified as Core
import Yves.TermF (SurfaceF (..), TermF)

newtype YTerm m v = MkTerm {getTerm :: Free TermF (Either m v)}

term :: YTerm m v -> Either (Either m v) (TermF (YTerm m (In v)) (YTerm m v))
term (MkTerm (Free.FVar v)) = Either.Left v
term (MkTerm (Free.FTerm t)) =
  Either.Right $ bimap (MkTerm . fmap In.ien) MkTerm t

pattern Var :: v -> YTerm m v
pattern Var v = MkTerm (Free.FVar (Either.Right v))

pattern MetaVar :: m -> YTerm m v
pattern MetaVar m = MkTerm (Free.FVar (Either.Left m))

pattern YTTerm :: TermF (YTerm m (In v)) (YTerm m v) -> YTerm m v
pattern YTTerm t <- (term -> Either.Right t)
  where
    YTTerm t = MkTerm $ Free.FTerm $ bimap (fmap In.ein . getTerm) getTerm t

pattern YTType :: Level -> YTerm m v
pattern YTType l = YTTerm (Sum.L2 (Core.TypeF l))

infixr 5 :~>:

pattern (:~>:) :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern a :~>: b = YTTerm (Sum.L2 (Core.PiF a b))

pattern YTAbs :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern YTAbs a f = YTTerm (Sum.L2 (Core.AbsF a f))

pattern (:@:) :: YTerm m v -> YTerm m v -> YTerm m v
pattern f :@: t = YTTerm (Sum.L2 (Core.AppF f t))

infixr 6 :*:

pattern (:*:) :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern a :*: b = YTTerm (Sum.L2 (Core.SigmaF a b))

pattern YTPair :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTPair b f s = YTTerm (Sum.L2 (Core.PairF b f s))

pattern YTFst :: YTerm m v -> YTerm m v
pattern YTFst p = YTTerm (Sum.L2 (Core.FstF p))

pattern YTBool :: YTerm m v
pattern YTBool = YTTerm (Sum.L2 Core.BoolTypeF)

pattern YTBValue :: Bool -> YTerm m v
pattern YTBValue b = YTTerm (Sum.L2 (Core.BoolValF b))

pattern YTIdType :: YTerm m v -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTIdType a l r = YTTerm (Sum.L2 (Core.IdTypeF a l r))

pattern YTRefl :: YTerm m v -> YTerm m v
pattern YTRefl p = YTTerm (Sum.L2 (Core.ReflF p))

pattern YTW :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern YTW a b = YTTerm (Sum.L2 (Core.WF a b))

pattern YTTree :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTTree b r s = YTTerm (Sum.L2 (Core.TreeF b r s))

pattern YTRec :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTRec g e s = YTTerm (Sum.L2 (Core.WRecF g e s))

pattern (:!:) :: YTerm m v -> YTerm m v -> YTerm m v
pattern te :!: ty = YTTerm (Sum.R2 (AscrF te ty))
