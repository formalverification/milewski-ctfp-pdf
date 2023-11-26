record Functor (F : Set → Set) : Set where
  field fmap : (A → B) → F A → F B

open Functor ⦃...⦄
