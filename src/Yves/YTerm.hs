{-# LANGUAGE PatternSynonyms #-}

module Yves.YTerm where

import Control.Monad.Scoped.Free (Free)
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In)
import Data.Bifunctor.Sum qualified as Sum
import Data.Bool (Bool)
import Yves.Core.Level (Level)
import Yves.Core.TermF qualified as Core
import Yves.TermF (SurfaceF (..), TermF)

type YTerm m = Free (TermF m)

pattern Var :: v -> YTerm m v
pattern Var v = Free.FVar v

pattern MetaVar :: m -> [YTerm m v] -> YTerm m v
pattern MetaVar m a = Free.FTerm (Sum.R2 (MetaVarF m a))

pattern YTType :: Level -> YTerm m v
pattern YTType l = Free.FTerm (Sum.L2 (Core.TypeF l))

infixr 5 :~>:

pattern (:~>:) :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern a :~>: b = Free.FTerm (Sum.L2 (Core.PiF a b))

pattern YTAbs :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern YTAbs a f = Free.FTerm (Sum.L2 (Core.AbsF a f))

pattern (:@:) :: YTerm m v -> YTerm m v -> YTerm m v
pattern f :@: t = Free.FTerm (Sum.L2 (Core.AppF f t))

infixr 6 :*:

pattern (:*:) :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern a :*: b = Free.FTerm (Sum.L2 (Core.SigmaF a b))

pattern YTPair :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTPair b f s = Free.FTerm (Sum.L2 (Core.PairF b f s))

pattern YTFst :: YTerm m v -> YTerm m v
pattern YTFst p = Free.FTerm (Sum.L2 (Core.FstF p))

pattern YTSnd :: YTerm m v -> YTerm m v
pattern YTSnd p = Free.FTerm (Sum.L2 (Core.SndF p))

pattern YTBool :: YTerm m v
pattern YTBool = Free.FTerm (Sum.L2 Core.BoolTypeF)

pattern YTBValue :: Bool -> YTerm m v
pattern YTBValue b = Free.FTerm (Sum.L2 (Core.BoolValF b))

pattern YTIf ::
  YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTIf g c t e = Free.FTerm (Sum.L2 (Core.IfF g c t e))

pattern YTIdType :: YTerm m v -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTIdType a l r = Free.FTerm (Sum.L2 (Core.IdTypeF a l r))

pattern YTRefl :: YTerm m v -> YTerm m v
pattern YTRefl p = Free.FTerm (Sum.L2 (Core.ReflF p))

pattern YTJ :: YTerm m v -> YTerm m v -> YTerm m (In v) -> YTerm m v
pattern YTJ g e r = Free.FTerm (Sum.L2 (Core.JF g e r))

pattern YTW :: YTerm m v -> YTerm m (In v) -> YTerm m v
pattern YTW a b = Free.FTerm (Sum.L2 (Core.WF a b))

pattern YTTree :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTTree b r s = Free.FTerm (Sum.L2 (Core.TreeF b r s))

pattern YTRec :: YTerm m (In v) -> YTerm m v -> YTerm m v -> YTerm m v
pattern YTRec g e s = Free.FTerm (Sum.L2 (Core.WRecF g e s))

pattern (:!:) :: YTerm m v -> YTerm m v -> YTerm m v
pattern te :!: ty = Free.FTerm (Sum.R2 (AscrF te ty))

type YType m = YTerm m
