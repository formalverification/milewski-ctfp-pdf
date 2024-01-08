instance
  contraOp : Contravariant (Op a)
  contraOp .fmap x y f (op g) = op (g ∘ f)
