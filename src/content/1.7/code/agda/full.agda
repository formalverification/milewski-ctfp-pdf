open import Data.Bool using (Bool; _∧_)
open import Data.Product using (_×_)
open import Data.Float
open import Function using (_∘_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable A B C R : Set

{- 7.1 Functors in Programming -}

{- 7.1.1 The Maybe Functor -}

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

{- 7.1.2 Equational Reasoning -}
id : A → A
id x = x

fmap : (A → B) → Maybe A → Maybe B
fmap _ Nothing = Nothing
fmap f (Just x) = Just (f x)

fmap-id-lemma : ∀ x → (fmap{B = A} id) x ≡ id x
fmap-id-lemma Nothing = refl
fmap-id-lemma (Just x) = refl

fmap-∘-lemma :  ∀{f : A → B}{g : B → C}
  →             (x : Maybe A) → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x
fmap-∘-lemma Nothing = refl
fmap-∘-lemma (Just x) = refl

{- 7.1.4 Typeclasses -}

{- A typeclass defines a family of types that support a common interface. For
instance, the class of objects that support equality is defined as follows:      -}
record Eq (A : Set) : Set where
  field _==_ : A → A → Bool

{- This definition states that type A is of the class Eq if it supports the
operator (==) that takes two arguments of type A and returns a Bool. If you want
to tell Agda that a particular type has such an equality, you have to declare it
an instance of this type class and provide the implementation of (==). For
example, given the definition of a 2D Point (a product type of two Floats):      -}
data Point : Set where
  Pt : Float → Float → Point

instance
  _ : Eq Float
  _ = record { _==_ = λ x y → does (x ≟ y) }

  _ : Eq Point
  _ = record { _==_ = eq }
        where
        open Eq ⦃...⦄
        eq : Point → Point → Bool
        eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂

record Functor (F : Set → Set) : Set₁ where
  field Fmap : (A → B) → F A → F B

instance  _ : Functor Maybe
          _ = record  { Fmap = λ f → λ where
                          Nothing → Nothing
                          (Just a) → Just (f a)
                      }


{- 7.1.6 The List Functor -}

data List (A : Set) : Set where
  Nil  : List A
  Cons : A → List A → List A

instance _ : Functor List
         _ = record { Fmap = list-fmap }
               where
               list-fmap : (A → B) → List A → List B
               list-fmap f Nil = Nil
               list-fmap f (Cons x as) = Cons (f x) (list-fmap f as)

instance _ : Functor λ A → (R → A)
         _ = record { Fmap = λ f g → f ∘ g }


{- 7.2 Functions as Containers -}


{- 7.3 Functor Composition -}

{- 7.4 Challenges -}
