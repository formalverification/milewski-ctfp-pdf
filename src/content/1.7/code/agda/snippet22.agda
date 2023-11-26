instance
  fromR : Functor λ A → (R → A)
  fromR .fmap = λ f g → f ∘ g
