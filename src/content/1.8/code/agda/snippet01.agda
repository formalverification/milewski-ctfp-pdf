record Bifunctor (F : Set → Set → Set) : Set₁ where
  field
    bimap : (A → C) → (B → D) → F A B → F C D
    first : (A → C) → F A B → F C B
    second : (B → D) → F A B → F A D
