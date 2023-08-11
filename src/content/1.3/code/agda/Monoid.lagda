\begin{code}
module Monoid where

-- Raw monoid ("raw" because the monoid laws are not included in the definition)
record RawMonoid {m : Set} : Set where
  field
    mempty   : m
    mappend  : m → m → m

\end{code}
