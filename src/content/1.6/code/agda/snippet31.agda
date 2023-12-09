maybeTail : List A → Maybe (List A)
maybeTail Nil = Nothing
maybeTail (Cons _ t) = Just t
