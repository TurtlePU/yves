module Yves.Core.Level (Level, max, succ, (<=)) where

import Data.Ord (max, (<=))
import Numeric.Natural (Natural)
import Prelude (succ)

type Level = Natural
