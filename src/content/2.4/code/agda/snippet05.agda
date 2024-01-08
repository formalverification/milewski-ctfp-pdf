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
