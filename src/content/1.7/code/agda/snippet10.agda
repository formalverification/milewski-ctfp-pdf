record Eq (A : Set) : Set where
  field _==_ : A → A → Bool

open Eq ⦃...⦄
