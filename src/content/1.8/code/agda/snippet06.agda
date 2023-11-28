instance
  _ : Functor Identity
  _ = record { fmap = fmap } where
    fmap : {A B : Set} → (A → B) → Identity A → Identity B
    fmap A→B (mkId a) = mkId (A→B a)
