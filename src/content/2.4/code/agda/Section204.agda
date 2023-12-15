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
{- We've seen that, for every choice of an object a in ℂ, we get a functor from ℂ
to 𝕊𝕖𝕥.  This kind of structure-preserving mapping to 𝕊𝕖𝕥 is often called a
representation.  We are representing objects and morphisms of ℂ as sets and
functions in 𝕊𝕖𝕥.

The functor ℂ(a, -) itself is sometimes called representable.  More generally, any
functor F that is naturally isomorphic to the hom-functor, for some choice of a,
is called representable.  Such a functor must necessarily be 𝕊𝕖𝕥-valued, since
ℂ(a, -) is.

I said before that we often think of isomorphic sets as identical.  More
generally, we think of isomorphic *objects* in a category as identical.  That's
because objects have no structure other than their relation to other objects (and
themselves) through morphisms.

For instance, we've previously talked about the category of monoids, 𝕄𝕠𝕟, that was
initially modeled with sets.  But we were careful to pick as morphisms only those
functions that preserved the monoidal structure of those sets.  So if two objects
in 𝕄𝕠𝕟 are isomorphic, meaning there is an invertible morphism between them, they
have exactly the same structure.  If we peeked at the sets and functions that they
were based upon, we'd see that the unit element of one monoid was mapped to the
unit element of another, and that a product of two elements was mapped to the
product of their mappings.

The same reasoning can be applied to functors.  Functors between two categories
form a category in which natural transformations play the role of morphisms.  So
two functors are isomorphic, and can be thought of as identical, if there is an
invertible natural transformation between them.

Let's analyze the definition of the representable functor from this
perspective. For F to be representable we require that: There
be an object a in ℂ$; one natural transformation $α$ from
ℂ(a, -) to F; another natural transformation, $\beta$, in
the opposite direction; and that their composition be the identity
natural transformation.

Let's look at the component of α at some object x.  It's a function in 𝕊𝕖𝕥:
α(x) : ℂ(a, x) → F x. The naturality condition for this transformation tells us
that, for any morphism f from $x$ to $y$, the following diagram
commutes: F f ∘ α(x) = α(y) ∘ ℂ(a, f)
In Haskell, we would replace natural transformations with polymorphic
functions:                                                           [snippet06] -}

{- with the optional ∀ quantifier. The naturality condition          [snippet07] -}

{- is automatically satisfied due to parametricity (it's one of those theorems for
free I mentioned earlier), with the understanding that fmap on the left is defined
by the functor F, whereas the one on the right is defined by the reader functor.
Since fmap for reader is just function precomposition, we can be even more
explicit.  Acting on h, an element of ℂ(a, x), the naturality condition simplifies
to:                                                                  [snippet08] -}

{- The other transformation, β, goes the opposite way:               [snippet09] -}

{- It must respect naturality conditions, and it must be the inverse of α:

                      α ∘ β = id = β ∘ α

We will see later that a natural transformation from ℂ(a, -)
to any 𝕊𝕖𝕥-valued functor always exists as long as F a is
non-empty (Yoneda's lemma) but it is not necessarily invertible.

Let me give you an example in Haskell with the list functor and Int as a.  Here's
a natural transformation that does the job:                          [snippet10] -}

{- We arbitrarily picked the number 12 and created a singleton list with it.  We
can then fmap the function h over this list and get a list of the type returned by
h.  (There are actually as many such transformations as there are list of integers.)

The naturality condition is equivalent to the composability of map (the list
version of fmap):                                                     [snippet11] -}

{- But if we tried to find the inverse transformation, we would have to go from a
list of arbitrary type x to a function returning x:                   [snippet12] -}

{- You might think of retrieving an x from the list, e.g., using head, but that
won't work for an empty list. Notice that there is no choice for the type a (in
place of Int) that would work here. So the list functor is not representable.

Remember when we talked about Haskell (endo-) functors being a little
like containers? In the same vein we can think of representable functors
as containers for storing memoized results of function calls (the
members of hom-sets in Haskell are just functions). The representing
object, the type a in ℂ(a, -), is thought of as the
key type, with which we can access the tabulated values of a function.
The transformation we called α is called tabulate, and its inverse, β, is called
index.  Here's a (slightly simplified) Representable class definition:
                                                                     [snippet13] -}

{- Notice that the representing type, our a, which is called Rep f here, is part
of the definition of Representable. The star just means that Rep f is a type (as
opposed to a type constructor, or other more exotic kinds).

Infinite lists, or streams, which cannot be empty, are representable.            -}
{-                                                                   [snippet14] -}

{- You can think of them as memoized values of a function taking an Integer as an
argument. (Strictly speaking, I should be using non-negative natural numbers, but
I didn't want to complicate the code.)

To tabulate such a function, you create an infinite stream of values.  Of course,
this is only possible because Haskell is lazy.  The values are evaluated on
demand.  You access the memoized values using index:                 [snippet15] -}

{- It's interesting that you can implement a single memoization scheme to
cover a whole family of functions with arbitrary return types.

Representability for contravariant functors is similarly defined, except
that we keep the second argument of ℂ(-, a) fixed.  Or, equivalently, we may
consider functors from ℂᵒᵖ to 𝕊𝕖𝕥, because ℂᵒᵖ(a, -) is the same as ℂ(-, a).

There is an interesting twist to representability. Remember that
hom-sets can internally be treated as exponential objects, in Cartesian
closed categories. The hom-set ℂ(a, x) is equivalent to
$x^a$, and for a representable functor F we can write: $-^a = F$.

Let's take the logarithm of both sides, just for kicks: $a = \mathbf{log}F$

Of course, this is a purely formal transformation, but if you know some
of the properties of logarithms, it is quite helpful. In particular, it
turns out that functors that are based on product types can be
represented with sum types, and that sum-type functors are not in
general representable (example: the list functor).

Finally, notice that a representable functor gives us two different
implementations of the same thing --- one a function, one a data
structure. They have exactly the same content --- the same values are
retrieved using the same keys. That's the sense of ``sameness'' I was
talking about. Two naturally isomorphic functors are identical as far as
their contents are involved. On the other hand, the two representations
are often implemented differently and may have different performance
characteristics. Memoization is used as a performance enhancement and
may lead to substantially reduced run times. Being able to generate
different representations of the same underlying computation is very
valuable in practice. So, surprisingly, even though it's not concerned
with performance at all, category theory provides ample opportunities to
explore alternative implementations that have practical value.     -}

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
