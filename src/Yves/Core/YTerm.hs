{-# LANGUAGE PatternSynonyms #-}

module Yves.Core.YTerm (module Yves.Core.TermF, module Yves.Core.YTerm) where

import Control.Monad.Scoped.Free (Free)
import Control.Monad.Scoped.Free qualified as Free
import Control.Monad.Scoped.Free.In (In)
import Data.Bool (Bool)
import Yves.Core.Level (Level)
import Yves.Core.TermF (TermF (..))

type YTerm = Free TermF

pattern Var :: v -> Free b v
pattern Var v = Free.FVar v

pattern YTType :: Level -> YTerm v
pattern YTType l = Free.FTerm (TypeF l)

infixr 5 :~>:

pattern (:~>:) :: YTerm v -> YTerm (In v) -> YTerm v
pattern a :~>: b = Free.FTerm (PiF a b)

pattern YTAbs :: Free TermF v -> Free TermF (In v) -> Free TermF v
pattern YTAbs b f = Free.FTerm (AbsF b f)

pattern (:@:) :: YTerm v -> YTerm v -> YTerm v
pattern f :@: t = Free.FTerm (AppF f t)

infixr 6 :*:

pattern (:*:) :: YTerm v -> YTerm (In v) -> YTerm v
pattern a :*: b = Free.FTerm (SigmaF a b)

pattern YTPair :: YTerm (In v) -> YTerm v -> YTerm v -> YTerm v
pattern YTPair b f s = Free.FTerm (PairF b f s)

pattern YTFst :: YTerm v -> YTerm v
pattern YTFst p = Free.FTerm (FstF p)

pattern YTBool :: YTerm v
pattern YTBool = Free.FTerm BoolTypeF

pattern YTBValue :: Bool -> YTerm v
pattern YTBValue b = Free.FTerm (BoolValF b)

pattern YTIdType :: YTerm v -> YTerm v -> YTerm v -> YTerm v
pattern YTIdType t l r = Free.FTerm (IdTypeF t l r)

pattern YTRefl :: YTerm v -> YTerm v
pattern YTRefl p = Free.FTerm (ReflF p)

pattern YTW :: YTerm v -> YTerm (In v) -> YTerm v
pattern YTW a b = Free.FTerm (WF a b)

pattern YTTree :: YTerm (In v) -> YTerm v -> YTerm v -> YTerm v
pattern YTTree b r s = Free.FTerm (TreeF b r s)

pattern YTWRec :: YTerm (In v) -> YTerm v -> YTerm v -> YTerm v
pattern YTWRec g e s = Free.FTerm (WRecF g e s)

type YType = YTerm
