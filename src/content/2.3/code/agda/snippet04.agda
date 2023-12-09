hom : (A → B) → Set
hom h = ∀ {a₁ a₂ : A} → h (a₁ *ᴬ a₂) ≡ h a₁ *ᴮ h a₂
