module full where

open import Data.Nat.Base as ℕ using ()
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; Σ-syntax) renaming (dmap′ to _⟨∘⟩_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Float using (Float) renaming (_<ᵇ_ to _<ᶠᵇ_)
open import Function using (_∘_; _∘₂_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


private variable A B C D E : Set

{- 9 Function Types  -------------------------------------------------------------}

{- 9.1 Universal Construction ----------------------------------------------------}
{- Paraphrasing the text:

   We will need a pattern that involves three objects: the function type that we
   are constructing, the domain type, and the codomain type.  The obvious pattern
   that connects these three types is called *function application* or
   *evaluation*. Given a candidate for a function type, let's call it Z (an
   object) and the domain type A (an object), the application maps this pair (Z,
   A) to the codomain type object B.  Thus, we have three objects, Z, A, and B;
   the latter two are fixed, but Z is merely a *candidate* for the function type
   we are trying to construct.

   We also have the application, a mapping. How do we incorporate this mapping
   into our pattern?  If we were allowed to look inside objects, we could pair a
   function f (an element of the proposed function type Z) with an argument x (an
   element of A) and map it to f x (the application of f to x, which inhabits B).

   But instead of dealing with individual pairs (f, x), we can talk about the
   whole *product* of the function type Z and argument type A. The product Z × A
   is an object, and we can pick as our application morphism an arrow g from that
   object to B. In Set, g would be the function that maps every pair (f, x) to f x.

           _______
     ---  |       |               ___
    | Z | | Z × A |  ---- g ---> | B |
     ---  |       |               ---
           -------
             ---
            | A |
             ---

   The pattern: A product of two objects Z, A, connected to another object B by a
   morphism g.

   Is this pattern specific enough to single out the function type using a
   universal construction? Not in every category, but in the categories of
   interest to us it is. And another question: Would it be possible to define a
   function object without first defining a product? There are categories in which
   there is no product, or there isn't a product for all pairs of objects. The
   answer is no: there is no function type, if there is no product type.

                 NO PRODUCT TYPE  ⇒  NO FUNCTION TYPE.

   Let's review the universal construction... we decree that Z together with the
   morphism g from Z × A to B is *better* than some other Z' with its own
   application g', if and only if there is a unique mapping h from Z' to Z such
   that the application of g' factors through the application of g.

   The third part of the universal construction is selecting the object that is
   universally the best. Let's call this object A → B.  This object comes with its
   own application---a morphism from A ⇒ B × A to B--- which we will call eval.
   The object A ⇒ B is the best if any other candidate for a function object Z'
   can be uniquely mapped to A ⇒ B in such a way that Z's application morphism g
   factorizes through eval. The object A ⇒ B with eval is better than any other
   object Z' and morphism g.



                _______
     ---       |       |
    | Z |      | Z × A |__
     ---       |       |  -- g __
      |         -------          \
      |            |              ↘ ---
      h          h × id            | B |
      |            |              ↗ ---
      |      _____ ↓ _____       /
   -- ↓ --  |             |  eval
  | A ⇒ B | | (A ⇒ B) × A |_/
   -------  |             |
             -------------
                  ---
                 | A |
                  ---

   A *function object* from A to B is an object A ⇒ B together with the morphism

                  eval : ((A ⇒ B) × A) → B

    such that for any other object Z with a morphism g : Z × A → B,

                  ∃! h : Z → (A ⇒ B)

    that factors g through eval:

                  g = eval ∘ (h × id).

   (We prove existence of such h below, after we define the "curry" and
   "factorizer" functions.)
                                                                                 -}


{- 9.2 Currying ------------------------------------------------------------------}
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


{- Existence of morphism h in universal property of function type ----------------}
eval : ((A → B) × A) → B
eval (f , a) = f a

→-univ-prop-existence' :  ∀ (Z : Set)(g : Z × A → B)
  →                      Σ[ h ∈ (Z → (A → B)) ]  g ≡ eval ∘ h ⟨∘⟩ id

→-univ-prop-existence' Z g = factorizer g , refl
{---------------------------------------------------------------------------------}


{- 9.3 Exponentials --------------------------------------------------------------}


{- 9.4 Cartesian Closed Categories -----------------------------------------------}
{- A category is called a "Cartesian closed category" provided it contains

+ a terminal object,
+ a product of every pair of objects,
+ an exponential for every pair of objects.

What's interesting about Cartesian closed categories from the perspective of
computer science is that they provide models for the simply typed lambda calculus,
which forms the basis of all typed programming languages.

The terminal object and the product have their duals: the initial object and the
coproduct. A Cartesian closed category that also supports those two, and in which
product can be distributed over coproduct

  A × (B + C) = (A × B) + (A × C)
  (B + C) × A = (B × A) + (C × A)

is called a "bicartesian closed category." We'll see in the next section that
bicartesian closed categories have some interesting properties.
                                                                                 -}

{- 9.5 Exponentials and Algebraic Data Types -------------------------------------}
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

{- 9.6 Curry-Howard Isomorphism --------------------------------------------------}
