record RawAdjunction (f : Set → Set) (u : Set → Set)
    ⦃ _ : Functor u ⦄
    ⦃ _ : Representable u ⦄ : Set₁ where
  field
    unit : a → u (f a)
    counit : f (u a) → a
