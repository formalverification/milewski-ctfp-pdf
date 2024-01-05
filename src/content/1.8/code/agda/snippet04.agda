instance
  orBifunc : Bifunctor Either
  orBifunc .bimap f _ (Left x) = Left (f x)
  orBifunc .bimap _ g (Right y) = Right (g y)
