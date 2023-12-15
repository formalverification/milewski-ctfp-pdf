record RawProfunctor (P : Set → Set → Set) : Set₁ where
  field
    dmap : (a → b) → (c → d) → P b c → P a d
    lmap : (a → b) → P b c → P a c
    rmap : (c → d) → P a c → P a d

record Profunctor (P : Set → Set → Set) : Set₁ where
  field
    p : RawProfunctor P
  open RawProfunctor p
  field
    dmap-prop : (f : a → b)(g : c → d) → dmap f g ≡ rmap g ∘ lmap f
    lmap-prop : (f : a → b) → lmap{c = c} f ≡ dmap f id
    rmap-prop : (f : c → d) → rmap{a = a} f ≡ dmap id f

instance
  arrowProfunctor : Profunctor _⇒_
  arrowProfunctor .p .dmap = λ ab cd bc → cd ∘ bc ∘ ab
  arrowProfunctor .p .lmap = λ x y z → y (x z)
  arrowProfunctor .p .rmap = λ x y z → x (y z)
  arrowProfunctor .dmap-prop _ _ = refl
  arrowProfunctor .lmap-prop _ = refl
  arrowProfunctor .rmap-prop _ = refl
