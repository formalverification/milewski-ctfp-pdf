uncurry : (A → B → C) → A × B → C
uncurry f (a , b) = f a b
