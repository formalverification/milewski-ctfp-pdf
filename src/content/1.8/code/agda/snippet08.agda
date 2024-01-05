Maybe : Set → Set
Maybe A = Either (Const ⊤ A) (Identity A)
