instance
  idFunctor : Functor Identity
  idFunctor .fmap f idA .identity = f (identity idA)
