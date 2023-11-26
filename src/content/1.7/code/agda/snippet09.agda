fmap-∘-lemma :  ∀{f : A → B}{g : B → C}
  →             (x : Maybe A)
  →             fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x
