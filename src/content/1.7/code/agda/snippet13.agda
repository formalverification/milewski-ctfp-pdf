record Functor (F : Set → Set) : Set where
  field Fmap : (A → B) → F A → F B

open Functor ⦃...⦄
