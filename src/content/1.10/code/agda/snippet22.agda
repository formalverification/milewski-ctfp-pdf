instance
  opContra : Contravariant (Op R)
  opContra .contramap f (op g) = op (g ∘ f)
