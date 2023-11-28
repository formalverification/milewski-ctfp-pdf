instance
    _ : Bifunctor _⊎_
    _ = record
        { bimap = bimap
        ; first = first
        ; second = second
        } where
        bimap : (A → C) → (B → D) → A ⊎ B → C ⊎ D
        bimap A→C _   (inj₁ a) = inj₁ (A→C a)
        bimap _   B→D (inj₂ b) = inj₂ (B→D b)

        first : {A B C : Set} → (A → C) → A ⊎ B → C ⊎ B
        first A→C (inj₁ a) = inj₁ (A→C a)
        first A→C (inj₂ b) = inj₂ b

        second : {A B D : Set} → (B → D) → A ⊎ B → A ⊎ D
        second B→D (inj₁ a) = inj₁ a
        second B→D (inj₂ b) = inj₂ (B→D b)
