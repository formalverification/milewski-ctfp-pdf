curry : (A × B → C) → A → B → C
curry f a b = f (a , b)
