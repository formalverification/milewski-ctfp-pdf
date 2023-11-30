factorizer : (A × B → C) → A → (B → C)
factorizer g = λ a → (λ b → g (a , b))
