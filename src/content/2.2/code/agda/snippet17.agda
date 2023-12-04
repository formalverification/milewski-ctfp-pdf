record ToString (A : Set) : Set where
  constructor toString
  field runToString : A → String
