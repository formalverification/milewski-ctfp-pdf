open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Int
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  A B C : Set
  f : A → B
  g : B → A

{- SECTION 5.1: INITIAL OBJECT ---------------------------------------------------
The *initial object* is the object with exactly one morphism going from it to
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the initial object is the empty set.
In Agda, we represent the empty set by the empty type ⊥.
-}
absurd : ⊥ → A
{- `absurd` denotes a family of morphism from ⊥ to any object A in Set.
Agda already defines this family and denotes it by `⊥-elim`
(read "false elimination").
-}
absurd = ⊥-elim
{- This is the familiar "ex falso quodlibet" principle: from a false premise
anything follows.
-}

{- SECTION 5.2: TERMINAL OBJECT --------------------------------------------------
The *terminal object* is the object with exactly one morphism coming to it from
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the terminal object is the singleton.
In Agda, we represent the singleton by the unit type ⊤.
-}
unit : A → ⊤
unit _ = tt

-- Here's another morphism (in Set) from any object to the two element set, Bool:
yes : A → Bool
yes _ = true
-- but Bool does not meet the uniqueness criterion of terminal object,
-- as there are other morphisms from every set to Bool; e.g.,
no : A → Bool
no _ = false

{- SECTION 5.4: ISOMORPHISMS -----------------------------------------------------
Morphism 𝑔 is the inverse of morphism 𝑓 if their composition is the
identity morphism. These are actually two equations because there are
two ways of composing two morphisms:
-}
_ : f ∘ g ≡ id
_ = {!!}
_ : g ∘ f ≡ id
_ = {!!}

{- SECTION 5.5: PRODUCTS ---------------------------------------------------------
The *product* of two objects `A` and `B` is an object `A × B` together with two
morphisms `π₁ : A × B → A` and `π₂ : A × B → B` such that for any object `C`
and morphisms `f : C → A`, `g : C → B` there is a unique morphism `h : C → A × B`
such that `f ≡ π₁ ∘ h` and `g ≡ π₂ ∘ h`.
-}
fst : A × B → A
fst (x , _) = x

snd : A × B → B
snd (_ , y) = y

{- Let's try to define a pattern of objects and morphisms in the category of sets
that will lead us to the construction of a product of two sets, `A` and `B`. This
pattern consists of an object `C` and two morphisms `p` and `q` connecting it to
`A` and `B`, respectively:
-}
p : C → A
p = {!!}
q : C → B
q = {!!}
{- All `C`s that fit this pattern will be considered candidates for the product.
There may be lots of them. For instance, let's pick, as our constituents, two
Haskell types, `Int` and `Bool`, and get a sampling of candidates for their product.
Here's one: `Int`. Can `Int` be considered a candidate for the product of `Int`
and `Bool`? Yes, it can---and here are its projections:
-}
p₁ : Int → Int
p₁ x = x
p₂ : Int → Bool
p₂ _ = true
{- Here's another one: (Int, Int, Bool). It's a tuple of three ele-
ments, or a triple. Here are two morphisms that make it a legitimate
candidate (we are using pattern matching on triples):
-}
p₃ : Int × Int × Bool → Int
p₃ (x , _ , _) = x
q₂ : Int × Int × Bool → Bool
q₂ (_ , _ , b) = b
{- Another way of looking at these equations is that m factorizes p' and q'.
-}
