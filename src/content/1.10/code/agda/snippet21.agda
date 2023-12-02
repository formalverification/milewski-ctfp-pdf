record Op (R : Set)(A : Set) : Set where
  constructor op
  field runOp : A → R
