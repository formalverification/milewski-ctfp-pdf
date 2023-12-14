record ToString (a : Set) : Set where
  constructor toString
  field runToString : a → String
