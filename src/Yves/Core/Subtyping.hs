module Yves.Core.Subtyping where

import Data.Bool (Bool)
import Yves.Core.YTerm (YType)
import Prelude qualified

infix 4 <:

(<:) :: YType v -> YType v -> Bool
(<:) = Prelude.error "TODO"
