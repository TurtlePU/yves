{-# LANGUAGE TypeOperators #-}

module Yves.Unification where

import Data.Collection (Collection (..))
import Yves.Elaboration.Monad (Elab)
import Yves.YTerm
import Prelude qualified

unify ::
  (Collection s, Key s ~ m) => YTerm m v -> YTerm m v -> Elab s v (YTerm m v)
unify = Prelude.error "TODO"
