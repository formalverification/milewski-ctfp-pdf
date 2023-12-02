length : List A → Const Int A
length [] = const 0ℤ
length (x ∷ xs) = const (1 + unConst (length xs))
