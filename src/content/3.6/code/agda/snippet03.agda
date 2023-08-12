record Monoid (m : Type 𝑢) : Set (usuc 𝑢) where
  field
    unit     : m
    _⊕_      : m → m → m

    ⊕right-unit : ∀ (x : m) → x ⊕ unit ≡ x
    ⊕left-unit  : ∀ (x : m) → unit ⊕ x ≡ x
    ⊕assoc      : ∀ (x y z : m) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
