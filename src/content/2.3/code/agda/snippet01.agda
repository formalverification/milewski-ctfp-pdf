record Monoid (A : Set) : Set where
  field
    mempty  :  A
    mappend :  A → A → A
    -- In Agda we can encode the laws that a monoid satisfies.
    idˡ    :  ∀ a → mappend mempty a ≡ a
    idʳ    :  ∀ a → mappend a mempty ≡ a
    assoc  :  ∀ a b c
              → mappend (mappend a b) c ≡ mappend a (mappend b c)
