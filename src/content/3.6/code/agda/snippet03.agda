record Monoid {m : Set} : Set where
  field
    mappend  : m → m → m
    mempty   : m
