record Monoid (A : Set) : Set where
  field
    mempty : A
    mappend : A → A → A
    -- In Agda we can encode the laws that a monoid satisfies.
    leftUnit : ∀{a} → mappend mempty a ≡ a
    righUnit : ∀{a} → mappend a mempty ≡ a
    assoc : ∀{a b c} → mappend (mappend a b) c ≡ mappend a (mappend b c)
