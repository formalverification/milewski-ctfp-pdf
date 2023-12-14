module Section108 where

open import Agda.Builtin.Unit
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a b c d : Set

{- 8.1 Bifunctors ----------------------------------------------------------------}
{-                                                                   [snippet01] -}
open import Function using (id; _∘_)

record Bifunctor (f : Set → Set → Set) : Set₁ where
  field
    bimap : (a → c) → (b → d) → f a b → f c d

  first : (a → c) → f a b → f c b
  first g = bimap g id

  second : (b → d) → f a b → f a d
  second h = bimap id h

  bimap-law : (a → c) → (b → d) → Set
  bimap-law g h =  (first g) ∘ (second h) ≡ bimap g h

-- open Bifunctor
{- 8.2 Product and Coproduct Bifunctors ------------------------------------------}
{-                                                                   [snippet02] -}
open import Data.Product using (_×_; _,_)

instance
  _ : Bifunctor _×_
  _ = record { bimap = bimap } where
      bimap : (a → c) → (b → d) → a × b → c × d
      bimap a→b c→d (a , c) = a→b a , c→d c

{-                                                                   [snippet03] -}
-- bimap : (a → c) → (b → d) → f a b → f c d

{-                                                                   [snippet04] -}
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)

-- standard Agda disjoint union

instance
  _ : Bifunctor _⊎_
  _ = record { bimap = bimap  } where
    bimap : (a → c) → (b → d) → a ⊎ b → c ⊎ d
    bimap a→c _   (inj₁ a) = inj₁ (a→c a)
    bimap _   b→d (inj₂ b) = inj₂ (b→d b)

-- alternative, more closely following Haskell

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

instance
  _ : Bifunctor Either
  _ = record { bimap = bimap } where
      bimap : (a → c) → (b → d) → Either a b → Either c d
      bimap f _ (Left x) = Left (f x)
      bimap _ g (Right y) = Right (g y)

-- {- 8.3 Functorial Algebraic Data Types -}

-- data Identity (A : Set) : Set where
--   mkId : A → Identity A

-- record Functor (F : Set → Set) : Set₁ where
--   constructor mkFunctor
--   field fmap : (A → B) → F A → F B

-- instance
--   _ : Functor Identity
--   _ = record { fmap = fmap } where
--     fmap : {A B : Set} → (A → B) → Identity A → Identity B
--     fmap A→B (mkId a) = mkId (A→B a)

-- module snippet07 where
--   data Maybe (A : Set) : Set where
--     Nothing : Maybe A
--     Just : A → Maybe A

-- data Const (C A : Set) : Set where
--   mkConst : C → Const C A

-- module snippet08 where
--   Maybe : Set → Set
--   Maybe A = Const ⊤ A ⊎ Identity A

-- private
--   variable
--     BF : Set → Set → Set
--     F G : Set → Set

-- module snippet09 where
--   record BiComp
--     (bf : Bifunctor BF)(fu : Functor F)(gu : Functor G) : Set where
--       constructor bicomp
--   -- data BiComp
--   --     (A B : Set)
--   --     (FU GU : Functor) :
--   --       Bifunctor where
--   --   bicomp : Set _

--   -- data BiComp (BF : Bifunctor) (FU GU : Functor) (A B : Set) : Set where
--   --   bicomp : BiComp ?
--   -- BiComp : ∀ (A B : Set) → (FU : Functor)(GU : Functor) → (BF : Bifunctor) → ?
--   -- BiComp = ?
--   -- BiComp : (BF : Bifunctor) → (FU GU : Functor) → (A B : Set) → Set → Set₂
--   -- BiComp = ?
--   -- BiComp : ∀ (A : Set) (B : Set)
--   --          → (FU : Functor) → (GU : Functor)
--   --          → (BF : Bifunctor)
--   --          → {! Functor  !}
--   -- BiComp = ? -- BF (FU A) (GU B)
