record Representable (f : Set → Set) : Set₁ where
  field
    Repf     : Set
    tabulate : (Repf → x) → f x
    index    : f x → Repf → x
