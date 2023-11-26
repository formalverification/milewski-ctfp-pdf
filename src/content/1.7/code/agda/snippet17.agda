fmap f Nil = Nil
fmap f (Cons x as) = Cons (f x) (list-fmap f as)
