{- 14 Representable Functors -----------------------------------------------------}

module Section204 where

open import Agda.Builtin.Nat using (_+_; _-_; _==_)
open import Data.Bool.Base               using (if_then_else_)
open import Data.Integer using (ℤ; 0ℤ; +_)
open import Data.List using (List; map; [_]) -- ; _∷_; head)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id; flip)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
private variable a b c d r u v w x y : Set

{- Main points from intro:
   - the set of all sets doesn't exist
   - the category of all sets, 𝕊𝕖𝕥, exists.
   - morphisms between any two objects in a category form a set (called hom-set)
   - cats where morphisms may form hom-objects (not hom-sets) are *enriched* cats
-}

{- 14.1 The Hom Functor ----------------------------------------------------------}
{- Every category comes equipped with a canonical family of mappings to 𝕊𝕖𝕥.
Those mappings are functors, so they preserve the structure of the category.

Fix a ∈ ℂ.  For each x ∈ ℂ, ℂ(a, x) is a set, so we have a mapping ℂ(a, -) : ℂ → 𝕊𝕖𝕥.

                        ℂ
                          a              𝕊𝕖𝕥
                        / | \
                       |  |  |
                        \ | /   ----→  ℂ(a, x)
                         ↘↓↙
                          x

(imho, the syntax λ x → ℂ(a, x) is nicer and clearer than ℂ(a, -))

If f : x → y in ℂ, then f is mapped to a function in ℂ(a, x) → ℂ(a, y)

          .→ x
         /   ↑ \
        /    |  \                      h   ℂ(a, x)
       h     |   \                     |
      /     /     \                    |
     /     /       \                   |
    a ====          f  -- ℂ(a, f) -->  |
     \     \       /                   |
      \     \     /                    ↓
      f∘h    \   /                    f∘h  ℂ(a, y)
        \    |  /
         \   ↓ ↙
          -→ y

                  ℂ(a, f) h = f ∘ h.

In Haskell, the hom-functor is better known as the Reader functor:   [snippet01] -}
data Reader a x : Set where
  reader : (a → x) → Reader a x

record Functor (F : Set → Set) : Set₁ where
  field fmap : {x y : Set} → (x → y) → F x → F y
{-                                                                   [snippet02] -}
module snippet02 where
  open Functor ⦃...⦄
  instance
    readerFunctor : Functor (Reader a)
    readerFunctor .fmap f (reader g) = reader (f ∘ g)

{- If we instead fix the target, we have the contravariant functor ℂ(-, a).
                                                                     [snippet03] -}
data Op a x : Set where
  op : (x → a) → Op a x

record Contravariant (F : Set → Set) : Set₁ where
  field fmap : {x y : Set} → (x → y) → F y → F x
{-                                                                   [snippet04] -}
module snippet04 where
  open Contravariant ⦃...⦄
  instance
    contraOp : Contravariant (Op a)
    contraOp .fmap f (op g) = op (g ∘ f)

{- If we let both objects vary, we get the *profunctor* ℂ(-, =), which is
contravariant in the first argument and covariant in the second.
                                                                     [snippet05] -}
record RawProfunctor (P : Set → Set → Set) : Set₁ where
  field  dmap : (a → b) → (c → d) → P b c → P a d
         lmap : (a → b) → P b c → P a c
         rmap : (c → d) → P a c → P a d
record Profunctor (P : Set → Set → Set) : Set₁ where
  field  p : RawProfunctor P
  open RawProfunctor p
  field  dmap-prop : (f : a → b)(g : c → d) → dmap f g ≡ rmap g ∘ lmap f
         lmap-prop : (f : a → b) → lmap{c = c} f ≡ dmap f id
         rmap-prop : (f : c → d) → rmap{a = a} f ≡ dmap id f
open RawProfunctor; open Profunctor
_⟶_ : Set → Set → Set
a ⟶ r = a → r
instance
  ⟶profunctor : Profunctor _⟶_
  ⟶profunctor .p .dmap = λ ab cd bc → cd ∘ bc ∘ ab
  ⟶profunctor .p .lmap = λ x y z → y (x z)
  ⟶profunctor .p .rmap = λ x y z → x (y z)
  ⟶profunctor .dmap-prop _ _ = refl
  ⟶profunctor .lmap-prop _ = refl
  ⟶profunctor .rmap-prop _ = refl

{-   IN EVERY CATEGORY, THE MAPPING OF OBJECTS TO HOM-SETS IS FUNCTORIAL.

                ℂ(-, =) : ℂᵒᵖ × ℂ → 𝕊𝕖𝕥                                           -}

{- 14.2 Representable Functors ---------------------------------------------------}
{- Any functor that is naturally isomorphic to a hom-functor ℂ(a, -), for some a,
is called *representable*.  Such a functor must necessarily be 𝕊𝕖𝕥-valued.

F is representable iff  F ≅ ℂ(a, -)  iff  there exist

  a ∈ ℂ,   α : ℂ(a, -) → F,   β : F → ℂ(a, -),

such that α ∘ β = id and β ∘ α = id.

At x ∈ ℂ, the component α(x): ℂ(a, x) → F x is a function in 𝕊𝕖𝕥.
The naturality condition: ∀ f : x → y,

  F f ∘ α(x) = α(y) ∘ ℂ(a, f).
                                                                     [snippet06] -}
module snippet06 {F : Set → Set} where
  α : ∀ x → (a → x) → F x
  α = {!!}

module snippet07 {a : Set}{f : x → y} where
  α : ∀{u v : Set} → Reader a u → Reader a v
  α = {!!}
  open snippet02
  open Functor {Reader a} readerFunctor
  {-                                                                 [snippet07] -}
  _ : fmap f ∘ α ≡ α ∘ fmap f
  _ = {!!}

module snippet08 {f : x → y}{h : a → x} where
  α : ∀{u : Set} → (a → u) → Reader a u
  α = reader
  open snippet02
  open Functor {Reader a} readerFunctor
  {-                                                                 [snippet08] -}
  _ : fmap f (α h) ≡ α (f ∘ h)
  _ = refl

module snippet09 {F : Set → Set} where
  β : ∀ x → F x → a → x
  β = {!!}

module snippet10 {F : Set → Set} where
  α : ∀{x : Set} → (ℤ → x) → List x
  α h = map h [ + 12 ]

module snippet11 {h : ℤ → x}{f : x → y} where
  _ : map f (map h [ + 12 ]) ≡ map (f ∘ h) [ + 12 ]
  _ = refl
  β : ∀{x : Set} → List x → (ℤ → x)
  β = {!!}
{-                                                                   [snippet13] -}
record Representable (f : Set → Set) : Set₁ where
  field
    Repf      : Set
    tabulate  : (Repf → x) → f x
    index     : f x → Repf → x
open Representable ⦃...⦄
{-                                                                   [snippet14] -}
data Stream (x : Set) : Set where
  Cons : x → Stream x → Stream x
{-                                                                   [snippet15] -}
instance
  repStream : Representable Stream
  repStream .Repf = ℕ
  repStream .tabulate f = Cons (f 0) (tabulate (f ∘ (_+ 1)))
  repStream .index (Cons b bs) n = if (n == 0) then b else index bs (n - 1)

