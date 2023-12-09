instance
  listMonoid : ∀ {A : Set} → Monoid (List A)
  listMonoid = record
                { mempty = []
                ; mappend = _++_
                ; leftId = λ _ → refl
                ; rightId = ++-identityʳ
                ; assoc = ++-assoc }
