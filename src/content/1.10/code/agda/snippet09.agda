safeHead (fmap f (x ∷ xs)) = safeHead (f x ∷ fmap f xs) = Just (f x)
