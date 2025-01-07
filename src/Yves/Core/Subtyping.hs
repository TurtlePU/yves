module Yves.Core.Subtyping where

import Data.Bool (Bool, (&&))
import Yves.Core.YTerm
import Yves.Core.Level ((<=))
import Data.Eq (Eq (..))

infix 4 <:

(<:) :: Eq v => YType v -> YType v -> Bool
YTType l <: YTType l' = l <= l'
a :~>: b <: a' :~>: b' = a' <: a && b <: b'
a :*: b <: a' :*: b' = a <: a' && b <: b'
YTIdType a l r <: YTIdType a' l' r' = a <: a' && (l, r) == (l', r')
YTW a b <: YTW a' b' = a <: a' && b' <: b
t <: u = t == u
