{- Chapter 10. Natural Transformations -------------------------------------------}

module Section110 where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.List.Instances
open import Data.Maybe.Instances
open import Effect.Functor
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open List
open Maybe

{- Functors are mappings between categories that preserve structure. -}

{- 10.1 Polymorphic Functions ----------------------------------------------------}

private variable
  A : Set
  F G : Set → Set
  f : A → A
{-                                                                   [snippet01] -}
module snippet01 where
  α : ∀{A} → F A → G A
  α = {!!}

{-                                                        [snippet02, snippet03] -}
module snippet02 where
  α : F A → G A
  α = {!!}

safeHead : List A → Maybe A
safeHead [] = nothing
safeHead (x ∷ xs) = just x

open RawFunctor
fmapᵐ = _<$>_ {ℓ = 0ℓ} maybeFunctor
fmapˡ = _<$>_ {ℓ = 0ℓ} listFunctor

{-                                                                   [snippet04] -}
nc : ∀ l → (fmapᵐ f ∘ safeHead) l  ≡  (safeHead ∘ fmapˡ f) l
nc [] = refl
nc (x ∷ l) = refl

{- 10.2 Beyond Naturality --------------------------------------------------------}

{- 10.3 Functor Category ---------------------------------------------------------}

{- 10.4 2-Categories -------------------------------------------------------------}

{- 10.5 Conclusion ---------------------------------------------------------------}

{- 10.6 Challenges ---------------------------------------------------------------}

{- 1. Define a natural transformation from the Maybe functor to the list functor.
      Prove the naturality condition for it.                                     -}

{- 2. Define at least two different natural transformations between Reader ()
      and the list functor. How many different lists of () are there?            -}

{- 3. Continue the previous exercise with Reader Bool and Maybe.                 -}

{- 4. Show that horizontal composition of natural transformation satisfies the
      naturality condition (hint: use components). It's a good exercise in
      diagram chasing.                                                           -}

{- 5. Write a short essay about how you may enjoy writing down the evident
      diagrams needed to prove the interchange law.                              -}

{- 6. Create a few test cases for the opposite naturality condition of
      transformations between different Op functors. Here's one choice:

      op : Op Bool Int
      op = Op (λ x → x > 0)

      f : String → Int
      f x = read x
                                                                                 -}
