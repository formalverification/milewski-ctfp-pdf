\begin{code}
module MonoidInstances where

open import Monoid
open import StringMonoid renaming (monoid to strMonoid)
open import Data.String
open RawMonoid

instance
  stringMonoid = strMonoid
\end{code}
