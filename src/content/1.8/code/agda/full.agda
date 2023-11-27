open import Data.Product using (_×_; _,_; proj₁; proj₂)

private variable A B C D : Set

{- 8.1 Bifunctor -}

record Bifunctor (F : Set → Set → Set) : Set₁ where
  field
    bimap : (A → C) → (B → D) → F A B → F C D
    first : (A → C) → F A B → F C B
    second : (B → D) → F A B → F A D

{- 8.2 Product and Coproduct Bifunctors -}

instance
    _ : Bifunctor _×_
    _ = record
        { bimap = bimap
        ; first = first
        ; second = second
        } where
        bimap : (A → C) → (B → D) → A × B → C × D
        bimap A→B C→D (a , c) = A→B a , C→D c
        first : {A C B : Set} → (A → C) → A × B → C × B
        first A→C (a , b) = A→C a , b
        second : {A B D : Set} → (B → D) → A × B → A × D
        second B→D (a , b) = a , B→D b
