instance _ : Functor λ A → (R → A)
         _ = record { Fmap = λ f g → f ∘ g }
