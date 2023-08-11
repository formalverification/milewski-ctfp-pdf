\begin{code}
module Section-1-3 where

open import Data.String

-- Raw monoid ("raw" because the monoid laws are not included in the definition)
record RawMonoid {m : Set} : Set where
  field
    mempty   : m
    mappend  : m → m → m

open RawMonoid ⦃ ... ⦄

instance
  strmonoid : RawMonoid {String}
  strmonoid .mempty = ""
  strmonoid .mappend = _++_


\end{code}
