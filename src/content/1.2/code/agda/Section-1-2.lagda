\begin{code}
module Section-1-2 where

open import Data.Integer using (ℤ ; 0ℤ)
open import Data.Bool using (Bool ; true ; false)

x : ℤ
x = 0ℤ

-- f could be, e.g., negation
f : Bool → Bool
f false = true
f true = false

-- ...which is more commonly denoted by ¬
¬ : Bool → Bool
¬ false = true
¬ true = false
\end{code}
