fmap _ Nil = Nil
fmap f (Cons x as) = Cons (f x) (fmap f as)
