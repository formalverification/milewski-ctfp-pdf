module full where

open import Data.Nat.Base as ℕ using ()
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Float using (Float) renaming (_<ᵇ_ to _<ᶠᵇ_)

private variable A B C : Set

{- 9 Function Types                                                              -}

{- 9.1 Universal Construction                                                    -}

{- 9.2 Currying                                                                  -}
{- A → (B → C)                                                       [snippet01] -}

{- A → B → C                                                         [snippet02] -}

{-                                                                   [snippet03] -}
catstr : String → String → String
catstr s s' = s ++ s'

{-                                                                   [snippet04] -}
catstr' : String → String → String
catstr' s = λ s' → s ++ s'

{-                                                                   [snippet05] -}
greet : String → String
greet = catstr "Hello "

{- A × B → C                                                         [snippet06] -}

{-                                                                   [snippet07] -}
curry : (A × B → C) → A → B → C
curry f a b = f (a , b)

{-                                                                   [snippet08] -}
uncurry : (A → B → C) → A × B → C
uncurry f (a , b) = f a b

{-                                                                   [snippet09] -}
factorizer : (A × B → C) → A → (B → C)
factorizer g = λ a → (λ b → g (a , b))

{- 9.3 Exponentials                                                              -}

{- 9.4 Cartesian Closed Categories                                               -}

{- 9.5 Exponentials and Algebraic Data Types                                     -}
data Either (A B : Set) : Set where
  Left  : A → Either A B
  Right : B → Either A B

-- Define a boolean version of less than for ℤ, as is done in the standard
-- library for weak inequality, _≤ᵇ_.
open import Agda.Builtin.Int public
  using () renaming ( Int     to ℤ
                    ; pos     to +_        -- "+ n"      stands for "n"
                    ; negsuc  to -[1+_] )  -- "-[1+ n ]" stands for "- (1 + n)"

_<ᵇ_ : ℤ → ℤ → Bool
-[1+ m ] <ᵇ -[1+ n ] = n ℕ.<ᵇ m
(+ m)    <ᵇ -[1+ n ] = false
-[1+ m ] <ᵇ (+ n)    = true
(+ m)    <ᵇ (+ n)    = m ℕ.<ᵇ n

{-                                                                   [snippet10] -}
f : Either ℤ Float → String
f (Left n) = if (n <ᵇ 0ℤ) then "Negative Int" else "Nonnegative Int"
f (Right n) = if (n <ᶠᵇ 0.0) then "Negative Float" else "Nonnegative Float"
