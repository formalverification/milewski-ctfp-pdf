module Section204 where

open import Function using (_∘_; id; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
private variable a b c d x r : Set

{- It's a known fact that the set of all sets doesn't exist, but the category of
all sets, 𝕊𝕖𝕥, does.  On the other hand, we assume that morphisms between any two
objects in a category form a set.  We even called it a hom-set.  To be fair, there
is a branch of category theory where morphisms don't form sets.  Instead they are
objects in another category.  Those categories that use hom-objects rather than
hom-sets, are called *enriched* categories.

A set is the closest thing to a featureless blob you can get outside of
categorical objects.  A set has elements, but you can't say much about these
elements.  If you have a finite set, you can count the elements.  You can kind of
count the elements of an infinite set using cardinal numbers.  The set of natural
numbers, for instance, is smaller than the set of real numbers, even though both
are infinite.  But, maybe surprisingly, a set of rational numbers is the same size
as the set of natural numbers.

Other than that, all the information about sets can be encoded in functions
between them---especially the invertible ones called isomorphisms.  For all
intents and purposes isomorphic sets are identical.  Before I summon the wrath of
foundational mathematicians, let me explain that the distinction between equality
and isomorphism is of fundamental importance.  In fact it is one of the main
concerns of the latest branch of mathematics, the Homotopy Type Theory (HoTT).   -}

{- 14.1 The Hom Functor ----------------------------------------------------------}
{- Every category comes equipped with a canonical family of mappings to 𝕊𝕖𝕥.
Those mappings are in fact functors, so they preserve the structure of the
category.  Let's build one such mapping.

Let's fix one object a in ℂ. For each object x in ℂ, the hom-set ℂ(a, x) is a set
(an object in 𝕊𝕖𝕥).  When we vary x keeping a fixed ℂ(a, x) will also
vary in 𝕊𝕖𝕥.  Thus we have a mapping from x to 𝕊𝕖𝕥.

  ℂ
     a              𝕊𝕖𝕥
   / | \
  |  |  | -----→  ℂ(a, x)
   \ | /
    ↘↓↙
     x

Viewing the hom-set as a mapping in its second argument, we use the notation
ℂ(a, -) with the dash serving as the placeholder for the argument.

(Better yet, λ x → ℂ(a, x) is even clearer.)

This mapping of objects is easily extended to the mapping of morphisms. Let's take
a morphism f in ℂ between two arbitrary objects x and y.  The object x is mapped to
the set ℂ(a, x), the object y to ℂ(a, y).  If this is to be a functor, f must be
mapped to a function between the two sets: ℂ(a, x) → ℂ(a, y)

Let's define this function point-wise.  For the argument we should pick an
arbitrary element of ℂ(a, x)---let's call it h.  Morphisms are composable if they
match end to end.  Since h ∈ ℂ(a, x), the codomain of h is the domain of f, so we
can compose the two functions; hence, f ∘ h ∈ ℂ(a, y).

      .→ x
     /   ↑ \
    /    |  \                   h   ℂ(a, x)
   h     |   \                  |
  /     /     \                 |
 /     /       \                |
a ====          f               |
 \     \       /                |
  \     \     /                 ↓
  f∘h    \   /                 f∘h  ℂ(a, y)
    \    |  /
     \   ↓ ↙
      -→ y

We have just found our function from ℂ(a, x) to ℂ(a, y), which will serve as the
image of f.  If there is no danger of confusion, we'll write this lifted function
as: ℂ(a, f) and its action on a morphism h as: ℂ(a, f) h = f ∘ h.

Since this construction works in any category, it must also work in the category
of Haskell types.  In Haskell, the hom-functor is better known as the Reader
functor:                                                             [snippet01] -}
data Reader a x : Set where
  reader : (a → x) → Reader a x

record Functor (F : Set → Set) : Set₁ where
  field fmap : (x y : Set) → (x → y) → F x → F y
open Functor ⦃...⦄
{-                                                                   [snippet02] -}
instance
  readerFunctor : Functor (Reader a)
  readerFunctor .fmap x y f (reader g) = reader (f ∘ g)

{- Now let's consider what happens if, instead of fixing the source of the hom-set,
we fix the target.  In other words, we're asking the question if the mapping
ℂ(-, a) is also a functor.  It is, but instead of being covariant, it's
contravariant.  That's because the same kind of matching of morphisms end to end
results in postcomposition by f; rather than precomposition, as was the case with
ℂ(a, -).  We have already seen this contravariant functor in Haskell.  We called
it Op:                                                               [snippet03] -}
data Op a x : Set where
  op : (x → a) → Op a x

record Contravariant (F : Set → Set) : Set₁ where
  field fmap : (x y : Set) → (x → y) → F y → F x
open Contravariant ⦃...⦄
{-                                                                   [snippet04] -}
instance
  contraOp : Contravariant (Op a)
  contraOp .fmap x y f (op g) = op (g ∘ f)

{- Finally, if we let both objects vary, we get a profunctor ℂ(-, =), which is
contravariant in the first argument and covariant in the second (to underline the
fact that the two arguments may vary independently, we use a double dash as the
second placeholder).  We have seen this profunctor before, when we talked about
functoriality:                                                       [snippet05] -}

record RawProfunctor (P : Set → Set → Set) : Set₁ where
  field
    dmap : (a → b) → (c → d) → P b c → P a d
    lmap : (a → b) → P b c → P a c
    rmap : (c → d) → P a c → P a d

record Profunctor (P : Set → Set → Set) : Set₁ where
  field
    p : RawProfunctor P
  open RawProfunctor p
  field
    dmap-prop : (f : a → b)(g : c → d) → dmap f g ≡ rmap g ∘ lmap f
    lmap-prop : (f : a → b) → lmap{c = c} f ≡ dmap f id
    rmap-prop : (f : c → d) → rmap{a = a} f ≡ dmap id f

open RawProfunctor
open Profunctor

_⇒_ : Set → Set → Set
a ⇒ r = a → r

instance
  arrowProfunctor : Profunctor _⇒_
  arrowProfunctor .p .dmap = λ ab cd bc → cd ∘ bc ∘ ab
  arrowProfunctor .p .lmap = λ x y z → y (x z)
  arrowProfunctor .p .rmap = λ x y z → x (y z)
  arrowProfunctor .dmap-prop _ _ = refl
  arrowProfunctor .lmap-prop _ = refl
  arrowProfunctor .rmap-prop _ = refl


{- The important lesson is that this observation holds in any category: the
mapping of objects to hom-sets is functorial.  Since contravariance is equivalent
to a mapping from the opposite category, we can state this fact succinctly as:

                ℂ(-, =) : ℂᵒᵖ × ℂ → 𝕊𝕖𝕥                                           -}

{- 14.2 Representable Functors ---------------------------------------------------}

{- 14.3 Challenges ---------------------------------------------------------------}

{- 1. Show that the hom-functors map identity morphisms in 𝒞 to corresponding
      identity functions in 𝕊𝕖𝕥.                                                 -}

{- 2. Show that Maybe is not representable.                                      -}

{- 3. Is the Reader functor representable?                                       -}

{- 4. Using Stream representation, memoize a function that squares its argument. -}

{- 5. Show that tabulate and index for Stream are indeed the inverse of each
      other. (Hint: use induction.)                                              -}

{- 6. The functor:  Pair a = Pair a a  is representable.  Can you guess the type
      that represents it? Implement tabulate and index.                          -}
