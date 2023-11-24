open import Data.Bool using (Bool; if_then_else_)
open import Data.Float using (Float; sqrt) renaming (_<ᵇ_ to _<_)
open import Data.Integer using (1ℤ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_)
open import Data.Rational using (ℚ; _/_)
open import Data.String using (String)
open import Function using (_∘_)

private variable A B C : Set

-- 1. Construct the Kleisli category for partial functions (define composition and identity).
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

morphism : Set → Set → Set
morphism A B = A → Maybe B

-- liftᵈᵒᵐ takes a function from A to Maybe B and lifts the domain to Maybe A,
--        thus returning a function from Maybe A to Maybe B.
liftᵈᵒᵐ : morphism A B → morphism (Maybe A) B
liftᵈᵒᵐ f nothing = nothing
liftᵈᵒᵐ f (just b) = f b

compose : morphism A B → morphism B C → morphism A C
compose f g = liftᵈᵒᵐ g ∘ f

id : morphism A A
id = just

-- 2. Implement the embellished function safe_reciprocal that returns
--    a valid reciprocal of its argument, if it’s different from zero.

safe-reciprocal : morphism ℕ ℚ
safe-reciprocal zero = nothing
safe-reciprocal (suc n) = just (1ℤ / suc n)

safe-root : morphism Float Float
safe-root x =
  if (x < 0.0) then nothing
  else just (sqrt x)

-- 3. Compose the functions safe_root and safe_reciprocal to implement
--    safe_root_reciprocal that calculates sqrt(1/x) whenever possible.
_>=>_ : morphism A B → morphism B C → morphism A C
m1 >=> m2 = (liftᵈᵒᵐ m2) ∘ m1

Writer : Set → Set
Writer = _× String

return : A → Writer A
return a = a , ""
