record Reader (E : Set) (A : Set) : Set where
  constructor reader
  field runReader : E → A
