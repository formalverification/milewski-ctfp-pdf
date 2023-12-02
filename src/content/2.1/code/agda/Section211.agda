module Section211 where

private variable
  A B C : Set

-- non-dependent version
_∘_ : (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

module snippet01 {g : A → B}{f : B → C} where
  h : A → C
  h = f ∘ g

module snippet02 {f : A → B}{g : B → C} where
  h : A → C
  h x = let y = f x
        in g y


-- dependent version
_∘ᵈ_ :  ∀{a b c}{A : Set a}{B : A → Set b}{C : {x : A} → B x → Set c}
  →     (∀{x}(y : B x) → C y) → (g : (x : A) → B x)
  →     ((x : A) → C (g x))
f ∘ᵈ g = λ x → f (g x)
