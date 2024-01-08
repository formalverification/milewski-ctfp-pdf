record RawAdjunction (f : Set → Set) (u : Set → Set)
    ⦃ _ : Functor u ⦄
    ⦃ _ : Representable u ⦄ : Set₁ where
  field
    leftAdjunct : (f a → b) → (a → u b)
    rightAdjunct : (a → u b) → (f a → b)
