module Section108 where

open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  A B C D : Set

{- 8.1 Bifunctors ----------------------------------------------------------------}
{-                                                                   [snippet01] -}
record Bifunctor (F : Set → Set → Set) : Set₁ where
  field
    bimap : (A → C) → (B → D) → F A B → F C D

  first : (A → C) → F A B → F C B
  first g = bimap g id

  second : (B → D) → F A B → F A D
  second = bimap id

  bimap-law : (A → C) → (B → D) → Set
  bimap-law g h =  (first g) ∘ (second h) ≡ bimap g h


open Bifunctor

{- 8.2 Product and Coproduct Bifunctors ------------------------------------------}
{-                                                                   [snippet02] -}
instance
  andBifunc : Bifunctor _×_
  andBifunc .bimap = λ f g (x , y) → f x , g y

{-                                                                   [snippet03] -}
{- bimap : (A → C) → (B → D) → A × B → C × D                                     -}

data Either (A B : Set) : Set where
  Left  : A → Either A B
  Right : B → Either A B

{-                                                                   [snippet04] -}
instance
  orBifunc : Bifunctor Either
  orBifunc .bimap f _ (Left x) = Left (f x)
  orBifunc .bimap _ g (Right y) = Right (g y)

{- 8.3 Functorial Algebraic Data Types -------------------------------------------}
{-                                                                   [snippet05] -}
record Identity (A : Set) : Set where
  field identity : A

record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  field
    fmap : (A → B) → F A → F B

open Functor
open Identity

{-                                                                   [snippet06] -}
instance
  idFunctor : Functor Identity
  idFunctor .fmap f idA .identity = f (identity idA)


{-                                                                   [snippet07] -}
module snippet07 where
  data Maybe (A : Set) : Set where
    Nothing : Maybe A
    Just : A → Maybe A

data Const (C A : Set) : Set where
  mkConst : C → Const C A

instance
  constFunc : Functor (Const C)
  constFunc .fmap = λ f → λ where (mkConst C) → mkConst C

{-                                                                   [snippet08] -}
Maybe : Set → Set
Maybe A = Either (Const ⊤ A) (Identity A)

{- Composition of functors is a functor.  What about bifunctor composition?
How does a composition of a bifunctor with two functors work on morphisms?
Given two morphisms, f and g, we lift f with functor F and g with functor G.
We then lift the resulting pair of lifted morphisms with the bifunctor. We can
express this composition in Haskell.

Let's define a data type that is parameterized by a bifunctor BF (it's a type
variable that is a type constructor that takes two types as arguments), two
functors Fu and Gu (type constructors that take one type variable each), and two
regular types A and B. We apply Fu to A and Gu to B, and then apply BF to the
resulting two types:                                                             -}

private variable
  BF : Set → Set → Set
  F G : Set → Set

{-                                                                   [snippet09] -}
record BiComp (bf : Bifunctor BF)(fu : Functor F)(gu : Functor G) : Set where
  constructor bicomp

BiComp' :  Bifunctor BF
  →        (Fu : (F : Set → Set → Set) → (A : Set) → Functor (F A))
  →        (Gu : (G : Set → Set → Set) → (B : Set) → Functor (G B))
  →        (F G : Set → Set → Set)
  →        (A B : Set) → Set
BiComp' BF Fu Gu F G A B = BiComp BF (Fu F A) (Gu G B)

{- The bimap function for the composition of a bifunctor with two functors is -}
--    bimap : (A → C) → (B → D) → F A B → F C D

{-                                                                   [snippet10] -}
instance
  biFuncFuncFunc :  {bf : Bifunctor BF}
                    {Fu : (F : Set → Set → Set) → (A : Set) → Functor (F A)}
                    {Gu : (G : Set → Set → Set) → (B : Set) → Functor (G B)}
    →               Bifunctor (BiComp' bf Fu Gu BF BF)

  bimap biFuncFuncFunc x x₁ x₂ = record {}

-- .bimap = λ _ _ → λ where bicomp → bicomp
