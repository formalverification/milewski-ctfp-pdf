instance
  listMonoid : ∀ {A : Set} → Monoid (List A)
  listMonoid = record
                { mempty = []
                ; mappend = _++_
                ; idˡ = λ _ → refl
                ; idʳ = ++-identityʳ
                ; assoc = ++-assoc }
