instance
  readerFunctor : Functor (Reader a)
  readerFunctor .fmap x y f (reader g) = reader (f ∘ g)
