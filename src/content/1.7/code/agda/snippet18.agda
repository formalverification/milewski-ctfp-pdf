instance _ : Functor List
         _ = record { Fmap = list-fmap }
               where
               list-fmap : (A → B) → List A → List B
               list-fmap f Nil = Nil
               list-fmap f (Cons x as) = Cons (f x) (list-fmap f as)
