open import Data.String

record Monoid {m : Set} : Set where
  field
    mempty   : m
    mappend  : m → m → m

open Monoid

StringMonoid : Monoid {String}
StringMonoid .mempty = ""
StringMonoid .mappend = _++_
