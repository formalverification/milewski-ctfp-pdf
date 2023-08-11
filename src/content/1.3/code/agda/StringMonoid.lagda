\begin{code}
module StringMonoid where

open import Monoid
open import Data.String
open RawMonoid

monoid : RawMonoid {String}
monoid .mempty = ""
monoid .mappend = _++_
\end{code}
