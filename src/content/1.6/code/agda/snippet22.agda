data OneOfThree (A B C : Set) : Set where
  Sinistral : A → OneOfThree A B C
  Medial    : B → OneOfThree A B C
  Dextral   : C → OneOfThree A B C
