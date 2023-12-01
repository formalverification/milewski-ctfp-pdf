safeHead : List A → Maybe A
safeHead [] = nothing
safeHead (x ∷ xs) = just x
