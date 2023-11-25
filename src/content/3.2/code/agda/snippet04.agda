record RawAdjunction (f : Set → Set) (u : Set → Set)
    ⦃ _ : Functor u ⦄
    ⦃ _ : Representable u ⦄ : Set₁ where
  field
    {- snippet 04 -}
    unit : a → u (f a)
    counit : f (u a) → a
