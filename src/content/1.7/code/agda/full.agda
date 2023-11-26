{-# OPTIONS --guardedness --sized-types #-}

open import Data.Bool using (Bool; _∧_)
open import Data.Product.Base as P using (Σ; _×_; _,_; <_,_>; proj₁; proj₂)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Float using (Float; _≟_)
open import Level using (Level)
open import Codata.Sized.Stream using (Stream; _∷_)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk as Thunk using (Thunk; force)

private variable
  a b c : Level
  A B C R : Set
  i : Size

{- 7.1 Functors in Programming -}

{- 7.1.1 The Maybe Functor -}

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

{- 7.1.2 Equational Reasoning -}
id : A → A
id x = x

fmap' : (A → B) → Maybe A → Maybe B
fmap' _ Nothing = Nothing
fmap' f (Just x) = Just (f x)

fmap-id-lemma : ∀ x → (fmap'{B = A} id) x ≡ id x
fmap-id-lemma Nothing = refl
fmap-id-lemma (Just x) = refl

-- non-dependent function composition
_∘_ : ∀ {A : Set} {B : Set} {C : Set} →
      (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)


fmap-∘-lemma :  ∀{f : A → B}{g : B → C}
  →             (x : Maybe A) → fmap' (g ∘ f) x ≡ (fmap' g ∘ fmap' f) x
fmap-∘-lemma Nothing = refl
fmap-∘-lemma (Just x) = refl

{- 7.1.4 Typeclasses -}

{- A typeclass defines a family of types that support a common interface. For
instance, the class of objects that support equality is defined as follows:      -}
record Eq (A : Set) : Set where
  field _==_ : A → A → Bool

open Eq ⦃...⦄

{- This definition states that type A is of the class Eq if it supports the
operator (==) that takes two arguments of type A and returns a Bool. If you want
to tell Agda that a particular type has such an equality, you have to declare it
an instance of this type class and provide the implementation of (==). For
example, given the definition of a 2D Point (a product type of two Floats):      -}
data Point : Set where
  Pt : Float → Float → Point

instance
  floatEq : Eq Float
  floatEq ._==_ = λ x y → does (x ≟ y)

  pointEq : Eq Point
  pointEq ._==_ = eq
    where
    eq : Point → Point → Bool
    eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂

record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  field fmap : (A → B) → F A → F B

open Functor ⦃...⦄
instance
  maybeFunctor : Functor Maybe
  maybeFunctor .fmap = λ f → λ where
    Nothing → Nothing
    (Just a) → Just (f a)

{- 7.1.6 The List Functor -}

data list (A : Set) : Set where
  Nil  : list A
  Cons : A → list A → list A

instance
  listFunc : Functor list
  listFunc .fmap _ Nil = Nil
  listFunc .fmap f (Cons x as) = Cons (f x) (fmap f as)

  fromR : Functor λ A → (R → A)
  fromR .fmap = _∘_


{- 7.2 Functions as Containers -}

infixr 5 _++_
_++_ : list A → Stream A i → Stream A i
Nil       ++ ys = ys
Cons x xs ++ ys = x ∷ (λ where .force → xs ++ ys)

unfold : (A → A × B) → A → Stream B i
unfold next seed =
  let (seed′ , b) = next seed in
  b ∷ λ where .force → unfold next seed′
iterate : (A → A) → A → Stream A ∞
iterate f = unfold < f , id >

nats : Stream ℕ ∞
nats = iterate suc zero


data Const (C A : Set) : Set where
  mkConst : C → Const C A

instance
  constFunc : Functor (Const C)
  constFunc .fmap = λ f → λ where (mkConst C) → mkConst C


{- 7.3 Functor Composition -}

open import Agda.Builtin.List
maybeTail : List A → Maybe (List A)
maybeTail [] = Nothing
maybeTail (x ∷ xs) = Just xs

open import Agda.Builtin.Int
open import Data.Integer
square : Int → Int
square x = x * x

mis : Maybe (List Int)
mis = Just (+ 1 ∷ + 2 ∷ + 3 ∷ [])
instance
  ListFunc : Functor List
  ListFunc .fmap _ [] = []
  ListFunc .fmap f (x ∷ as) = (f x) ∷ (fmap f as)

mis2 : Maybe (List Int)
mis2 = fmap (fmap square) mis

mis2' : Maybe (List Int)
mis2' = (fmap ∘ fmap) square mis
