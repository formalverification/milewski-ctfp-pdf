{- Chapter 12. Limits and Colimits -}

module Section212 where

open import Agda.Builtin.Float
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Integer
open import Data.String
open import Data.Unit
-- open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- private variable
--   A B C C' D : Set

{- The construction of a product starts with the selection of two objects A and B,
whose product we want to construct.  But what does it mean to select objects? Can
we rephrase this action in more categorical terms?  Two objects form a pattern---a
very simple pattern.  We can abstract this pattern into a category---a very simple
category, but a category nevertheless.  It's a category that we'll call 𝟚. It
contains just two objects, 1 and 2, and no morphisms other than the two obligatory
identities.  Now we can rephrase the selection of two objects in C as the act of
defining a functor 𝒟 from the category 2 to ℂ.  A functor maps objects to objects,
so its image is just two objects (or it could be one, if the functor collapses
objects, which is fine too). It also maps morphisms---in this case it simply maps
identity morphisms to identity morphisms.

What's great about this approach is that it builds on categorical notions,
eschewing the imprecise descriptions like "selecting objects," taken straight from
the hunter-gatherer lexicon of our ancestors. And, incidentally, it is also easily
generalized, because nothing can stop us from using categories more complex than 𝟚
to define our patterns.

But let's continue.  The next step in the definition of a product is the selection
of the candidate object C.  Here again, we could rephrase the selection in terms
of a functor from a singleton category.  And indeed, if we were using Kan
extensions, that would be the right thing to do.  But since we are not ready for
Kan extensions yet, there is another trick we can use: a constant functor Δ from
the same category 𝟚 to ℂ.  The selection of C in ℂ can be done with Δ_C. Remember,
Δ_C maps all objects into C and all morphisms into id_C.

Now we have two functors, Δ_C and 𝒟 going between 𝟚 and ℂ so it's only natural to
ask about natural transformations between them.  Since there are only two objects
in 𝟚, a natural transformation will have two components.  Object 1 in 𝟚 is mapped
to C by Δ_C and to A 𝒟.  So the component of a natural transformation between Δ_C
and 𝒟 at 1 is a morphism from C to A.  Call it p.  The second component is a
morphism q from C to B---the image of the object 2 in 𝟚 under 𝒟.  But these are
exactly like the two projections we used in our original definition of the
product.  So instead of talking about selecting objects and projections, we can
talk about picking functors and natural transformations.  It so happens that in
this simple case the naturality condition for our transformation is trivially
satisfied, because there are no morphisms (other than the identities) in 𝟚.

A generalization of this construction to categories other than 𝟚---ones that, for
instance, contain non-trivial morphisms---will impose naturality conditions on the
transformation between Δ_C and 𝒟.  We call such a transformation a *cone*, because
the image of Δ is the apex of a cone/pyramid whose sides are formed by the
components of the natural transformation. The image under 𝒟 forms the base of the
cone.

In general, to build a cone we start with a category 𝕀 that defines the pattern.
It's a small, often finite category.  We pick a functor 𝒟 from 𝕀 to ℂ and call it
(or its image) a *diagram*.  We pick some C in ℂ as the apex of our cone. We use
it to define the constant functor Δ_C from 𝕀 to ℂ.  A natural transformation from
Δ_C to 𝒟 is then our cone.  For a finite 𝕀 it's just a bunch of morphisms
connecting C to the diagram: the image of 𝕀 under 𝒟.

Naturality requires that all triangles (the walls of the pyramid) in this diagram
commute.  Indeed, take any morphism f in 𝕀.  The functor 𝒟 maps f to a morphism
𝒟 f in ℂ, a morphism that forms the base of some triangle. The constant functor
Δ_C maps f to the identity morphism on C.  Δ_C squishes the two ends of the
morphism into one object, and the naturality square becomes a commuting triangle.
The two arms of this triangle are the components of the natural transformation.
So that's one cone.  What we are interested in is the *universal cone*---just like
we picked a universal object for our definition of a product.

There are many ways to go about it. For instance, we may define a *category of
cones* based on a given functor 𝒟.  Objects in that category are cones.  Not every
object C in ℂ can be an apex of a cone, though, because there may be no natural
transformation between Δ_C and 𝒟.

To make it a category, we also have to define morphisms between cones. These would
be fully determined by morphisms between their apexes. But not just any morphism
will do. Remember that, in our construction of the product, we imposed the
condition that the morphisms between candidate objects (the apexes) must be common
factors for the projections. For instance:
                                                                                 -}
_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

module snippet01 {A B C C' : Set} where
  p : C → A; q : C → B; m : C' → C
  p = {!!}; q = {!!}; m = {!!}
  p' : C' → A; q' : C' → B

  {-                                                                 [snippet01] -}
  p' = p ∘ m
  q' = q ∘ m

{- This condition translates, in the general case, to the condition that the
triangles whose one side is the factorizing morphism all commute.  We'll take
those factorizing morphisms as the morphisms in our category of cones.  It's easy
to check that those morphisms indeed compose, and that the identity morphism is a
factorizing morphism as well.  Cones therefore form a category.

Now we can define the universal cone as the *terminal object* in the category of
cones.  The definition of the terminal object states that there is a unique
morphism from any other object to that object.  In our case it means that there is
a unique factorizing morphism from the apex of any other cone to the apex of the
universal cone.  We call this universal cone the *limit* of the diagram D, Lim[D]
(in the literature, you'll often see a left arrow pointing towards 𝕀 under the Lim
sign). Often, as a shorthand, we call the apex of this cone the limit (or the
limit object).

         --[ Lim[D] is the universal (or "best") cone for D. ]--

The intuition is that the limit embodies the properties of the whole diagram in a
single object.  For instance, the limit of our two-object diagram is the product
of two objects.  The product (together with the two projections) contains the
information about both objects. And being universal means that it has no
extraneous junk.
                                                                                 -}
{- 12.1 Limit as a Natural Isomorphism  ------------------------------------------}
{- There is still something unsatisfying about this definition of a limit.  It's
workable, but we still have this commutativity condition for the triangles that
are linking any two cones.  It would be so much more elegant if we could replace
it with some naturality condition.

We are no longer dealing with one cone but with a whole category of cones. If the
limit happens to exist, then one of those cones is the universal cone (with apex
Lim[D]).  For every other cone there is a unique factorizing morphism that maps
its apex to Lim[D].  To reiterate, with each cone is associated a unique morphism
mapping it's apex to Lim[D], so we have a mapping of cones to morphisms, and it's
a one-to-one mapping.

This special morphism is a member of the hom-set ℂ(C, Lim[D]).  The other members
of ℂ(C, Lim[D]) are less fortunate in the sense that they don't factorize the
mapping of the two cones.  What we want is to be able to pick, for each C, one
morphism from the set ℂ(C, Lim[D])---a morphism that satisfies the particular
commutativity condition.  That sounds like defining a natural transformation!

But what functors are related by this transformation?  One functor maps C to the
set ℂ(C, Lim[D]); since C ∈ ℂ and ℂ(C, Lim[D]) ∈ 𝕊𝕖𝕥, it's a functor from ℂ to 𝕊𝕖𝕥
---it maps objects to sets.  In fact it's a contravariant functor.  Here's how we
define its action on morphisms: take a morphism from C' to C, say, f : C' → C.
Our functor maps C' to the set ℂ(C', Lim[D]).  To define the action of this
functor on f (to "lift" f), we have to define the corresponding mapping between
ℂ(C, Lim[D]) and ℂ(C', Lim[D]). (Notice that the functor has type
(C' → C) → ℂ(C, Lim[D]) → ℂ(C', Lim[D]) in this case.)

So, let's pick one element u of ℂ(C, Lim[D]) and see if we can map it to some
element of ℂ(C', Lim[D]).  We have u : C → Lim[D], and we can compose u with f to
get: u ∘ f : C' → Lim[D], an element of ℂ(C', Lim[D]), so we have found a mapping
of morphisms.                                                                    -}
module snippet02 {C C' LimD : Set} where
  {-                                                                 [snippet02] -}
  contramap : (C' → C) → (C -> LimD) → (C' -> LimD)
  contramap f u = u ∘ f

{- To define a natural transformation, we need another functor that's also a
mapping from ℂ to 𝕊𝕖𝕥.  But this time we'll consider a set of cones.  Cones are
just natural transformations; in the present case, we're looking at the set
Nat(Δ_C, D) of natural transformations.  The mapping from C to Nat(Δ_C, D)
is a (contravariant) functor.  How can we show that?  Again, let's define its
action on a morphism, say, f : C' → C.  The lifting of f should be a mapping of
natural transformations between two functors that go from 𝕀 to ℂ:

            Nat(Δ_C, D) → Nat(Δ_C', D)

How do we map natural transformations?  Every natural transformation is a family
of morphisms, one for each element of 𝕀.  A component of some α ∈ Nat(Δ_C, D)) at
A ∈ 𝕀ₒ is a morphism,
                        α(A) : Δ_C A → D A,

or, using the definition of the constant functor Δ, α(A) : C → D A. Given f and α,
we construct β ∈ Nat(Δ_C', D) with A-component β(A) : C' → D A.  We can easily get
the latter from the former by composing with f, β(A) = α(A) ∘ f, and it's easy to
show that the family β so defined yields a natural transformation.

Thus, given a morphism f, we built a mapping between two natural transformations,
component-wise. This mapping defines contramap for the functor C → Nat(Δ_C, D).
Thus we have two (contravariant) functors from ℂ to 𝕊𝕖𝕥, and we haven't even made
any assumptions---these functors always exist!

Now that we have two functors, we can talk about natural transformations between
them.  So without further ado, here's the conclusion: A functor D from 𝕀 to ℂ has
a limit Lim[D] iff there is a natural isomorphism ℂ(C, Lim[D]) ≃ Nat(Δ_C, D)
between the two functors just defined.                                           -}

{- 12.2 Examples of Limits  ------------------------------------------------------}
{- We've seen that the categorical product is a limit of a diagram generated by a
simple category we called 𝟚.

Another interesting limit is the *equalizer*, the limit generated by a two-element
category with two parallel morphisms going between them.  This category selects a
diagram in ℂ consisting of two objects (A, B) and two morphisms (f, g):          -}
module snippet03 {A B C : Set} where
  {-                                                                 [snippet03] -}
  f : A → B
  g : A → B

  f = {!!}; g = {!!}

{- To build a cone over this diagram, we have to add the apex, C and two
projections:
               C
             /   \
            p     q
           /       \
          /  _ f _  \
         ↓ /       ↘ ↓
         A --- g --→ B

                                                                     [snippet04] -}
  p : C → A
  q : C → B

  p = {!!}; q = {!!}

{- We have two triangles that must commute:
                                                                     [snippet05] -}
  _ : q ≡ f ∘ p
  _ = {!!}
  _ : q ≡ g ∘ p
  _ = {!!}

{- This tells us that q is uniquely determined by one of these equations, say, q ≡
f ∘ p, and we can omit it from the picture. So we are left with just one condition:
                                                                     [snippet06] -}
  _ : f ∘ p ≡ g ∘ p
  _ = {!!}

{- The way to think about it is that, if we restrict our attention to 𝕊𝕖𝕥, the
image of the function p selects a subset of A.  When restricted to this subset,
the functions f and g are equal.

For instance, take A to be the two-dimensional plane parameterized by coordinates
x and y.  Take B to be the real line, and take:
                                                                                 -}
module snippet07 where
  f : ℤ × ℤ → ℤ
  g : ℤ × ℤ → ℤ

  {-                                                                 [snippet07] -}
  f (x , y) = + 2 * y + x
  g (x , y) = y - x

  {- The equalizer for these two functions is the set of real numbers (the apex,
  C) and the function:                                                           -}
  p : ℤ → ℤ × ℤ
  {-                                                                 [snippet08] -}
  p t = (t , - (+ 2 * t))

  {- Notice that p t defines a straight line in the two-dimensional plane.  Along
  this line, the two functions are equal.

  Of course, there are other sets C' and functions p' that may lead to the
  equality:                                                                      -}
  p' : ⊤ → ℤ × ℤ
  {-                                                                 [snippet09] -}
  _ : f ∘ p' ≡ g ∘ p'
  _ = {!!}
  {- but they all uniquely factor out through p.  For instance, we can take the
  singleton set ⊤ as C' and the function:
                                                                     [snippet10] -}
  p' tt = (0ℤ , 0ℤ)

  {- It's a good cone, because f (0 , 0) = g (0 , 0).  But it's not universal,
  because of the unique factorization through h:                                 -}
  h : ⊤ → ℤ
  {-                                                                 [snippet11] -}
  _ : p' ≡ p ∘ h
  _ = {!!}

  {- with                                                            [snippet12] -}
  h ⊤ = 0ℤ

{- An equalizer can thus be used to solve equations of the type f x = g x.  But
it's much more general, because it's defined in terms of objects and morphisms
rather than algebraically.

An even more general idea of solving an equation is embodied in another
limit---the pullback.  Here, we still have two morphisms that we want to equate,
but this time their domains are different.  We start with a three-object category
of the shape: 1 →  2 ← 3. The diagram corresponding to this category consists of
three objects, A, B, C, and two morphisms:                                       -}
module snippet13 {A B C D : Set} where
  {-                                                                 [snippet13] -}
  f : A → B
  g : C → B
  f = {!!}; g = {!!}

  {- This diagram is often called a *cospan*.  A cone built on top of this diagram
  consists of the apex, D, and three morphisms:                      [snippet14] -}
  p : D → A
  q : D → C
  r : D → B
  p = {!!}; q = {!!}; r = {!!}

  {-


      A -- f --→ B ←-- g -- C  cospan: three objects (A, B, C) and two morphisms
                                       (f : A → B ← C : g)


                 D             cone: an apex (D) and three morphisms (p, r, q).
               / | \
              p  |  q
             /   |   \
            ↙    |    ↘
           A     r     C
            \    |    /
             f   |   g
              \  |  /
               ↘ ↓ ↙
                 B

  Commutativity conditions tell us that r is completely determined by the other
  morphisms, and can be omitted from the picture.  So we are only left with the
  following condition:                                               [snippet15] -}
  _ : g ∘ q ≡ f ∘ p
  _ = {!!}

{- A *pullback* is a universal cone of this shape.

                 D'
               / . \
              /  .  \
             /   .   \
            /    ↓    \
           /     D     \
          p'   /   \    q'
          |   p     q   |
          |  /       \  |
          ↓ ↙         ↘ ↓
           A           C
            \         /
             f       g
              \     /
               ↘   ↙
                 B

Again, if you narrow your focus down to sets, you can think of the object D as
consisting of pairs of elements from A and C for which f acting on the first
component is equal to g acting on the second component.
                                                                                 -}
module snippet16 {A : Set} where
  f : A → Float; f = {!!}

  {- If the above is still too general, consider the special case in which g is a
  constant function, say g _ = 1.23 (assuming that B is a set of real numbers).
  Then you are really solving the equation:                          [snippet16] -}
  _ : ∃[ x ] f x ≡ 1.23
  _ = {!!}


{- 12.3 Colimits -----------------------------------------------------------------}
{- Just like all constructions in category theory, limits have their dual image in
opposite categories. When you invert the direction of all arrows in a cone, you
get a co-cone, and the universal one of those is called a colimit. Notice that the
inversion also affects the factorizing morphism, which now flows from the
universal co-cone to any other co-cone.

A typical example of a colimit is a coproduct, which corresponds to the diagram
generated by 𝟚, the category we used earlier in the definition of the product.

Both the product and the coproduct embody the essence of a pair of objects, each
in a different way.  Just like the terminal object was a limit, so the initial
object is a colimit corresponding to the diagram based on an empty category.

The dual of the pullback is called the *pushout*. It's based on a diagram called a
span, generated by the category 1 ← 2 → 3.                                       -}

{- 12.4 Continuity ---------------------------------------------------------------}
{- Functors come close to the idea of continuous mappings of categories, in the
sense that they never break existing connections (morphisms).  The actual
definition of a *continuous functor* F from a category ℂ to ℂ' includes the
requirement that the functor preserve limits. Every diagram D in ℂ can be mapped
to a diagram F ∘ D in ℂ' by simply composing two functors.  The continuity
condition for F states that, if the diagram D has a limit Lim[D], then the diagram
F ∘ D also has a limit, and it is equal to F(Lim[D]).

Notice that, because functors map morphisms to morphisms, and compositions to
compositions, an image of a cone is always a cone.  A commuting triangle is always
mapped to a commuting triangle (functors preserve composition).  The same is true
for the factorizing morphisms: the image of a factorizing morphism is also a
factorizing morphism.  So every functor is *almost* continuous.  What may go wrong
is the uniqueness condition.  The factorizing morphism in ℂ' might not be
unique.  There may also be other "better" cones in ℂ' that weren't available in ℂ.

A hom-functor is an example of a continuous functor.  Recall that the hom-functor,
ℂ(A, B), is contravariant in the first variable and covariant in the second.  In
other words, it's a functor: ℂᵒᵖ × ℂ → 𝕊𝕖𝕥.  When its second argument is fixed,
the hom-set functor (which becomes the representable presheaf) maps colimits in
ℂ to limits in 𝕊𝕖𝕥; and when its first argument is fixed, it maps limits to
limits.

In Haskell, a hom-functor is the mapping of any two types to a function type, so
it's just a parameterized function type.  When we fix the second parameter to,
say, String, we get the contravariant functor:                                   -}
module snippet17 {A B : Set} where
  {-                                                                 [snippet17] -}
  record ToString (A : Set) : Set where
    constructor toString
    field runToString : A → String

  record Contravariant (F : Set → Set) : Set₁ where
    constructor contravariant
    field contramap : (B → A) → (F A -> F B)

  open Contravariant ⦃...⦄

  instance
    tostring : Contravariant ToString
    tostring .contramap f (toString g) = toString (g ∘ f)

{- Continuity means that when ToString is applied to a colimit, for instance the
coproduct Either B C, it will produce a limit; in this case a product of two
function types:

ToString (Either B C) ~ (B → String, C → String)                     [snippet18] -}

{- Indeed, any function of Either b c is implemented as a case statement with the
two cases being serviced by a pair of functions.

Similarly, when we fix the first argument of the hom-set, we get the familiar
reader functor. Its continuity means that, for instance, any function returning a
product is equivalent to a product of functions; in particular:                  -}
{-                                                                   [snippet19] -}
{- r → A × B ~ (R → A , R → B)                                                   -}

{- I know what you're thinking: You don't need category theory to figure these
things out. And you're right! Still, I find it amazing that such results can be
derived from first principles with no recourse to bits and bytes, processor
architectures, compiler technologies, or even lambda calculus.

If you're curious where the names "limit" and "continuity" come from, they are a
generalization of the corresponding notions from calculus. In calculus limits and
continuity are defined in terms of open neighborhoods. Open sets, which define
topology, form a category (a poset).                                             -}
p
{- 12.5 Challenges ---------------------------------------------------------------}

{- 1. How would you describe a pushout in the category of C++ classes?           -}
{- 2. Show that the limit of the identity functor Id : 𝒞 → 𝒞 is the initial
      object.                                                                    -}
{- 3. Subsets of a given set form a category. A morphism in that category is
      defined to be an arrow connecting two sets if the first is the subset
      of the second. What is a pullback of two sets in such a category?
      What's a pushout? What are the initial and terminal objects?               -}
{- 4. Can you guess what a coequalizer is?                                       -}
{- 5. Show that, in a category with a terminal object, a pullback towards the
      terminal object is a product.                                              -}
{- 6. Similarly, show that a pushout from an initial object (if one exists) is
      the coproduct.                                                             -}
