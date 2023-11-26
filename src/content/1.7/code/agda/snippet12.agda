instance
  _ : Eq Float
  _ = record { _==_ = λ x y → does (x ≟ y) }

  _ : Eq Point
  _ = record { _==_ = eq }
        where
        open Eq ⦃...⦄
        eq : Point → Point → Bool
        eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂
