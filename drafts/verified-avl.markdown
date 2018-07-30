---
title: Verified AVL Trees in Haskell and Agda
tags: Haskell, Agda
bibliography: AVL.bib
---

I've been writing a lot of Agda recently, and had the occasion to write a
[Fenwick tree](https://en.wikipedia.org/wiki/Fenwick_tree) with some
rebalancing. I decided to use an AVL tree to rebalance the structure, rather
than a red-black tree, for two reasons:

#. AVL trees seem to perform better than red-black trees in practice
[@pfaff_performance_2004].
#. The Agda standard library [@danielsson_agda_2018] has an implementation of
AVL trees already.

After watching a talk by Stephanie Weirich [-@weirich_depending_2014] on
comparing a verified implementation of red-black trees in Haskell and Agda, I
thought I'd do the same here for AVL trees. My implementation of AVL trees is
actually a little different from the one in the Agda standard library, although
for the ordering proofs it uses the same technique, from Conor McBride
[-@mcbride_how_2014].

# Height

AVL trees are more strictly balanced than red-black trees: the height of
neighboring subtrees can differ by at most one. To store the height, we will
start as every dependently-typed program does: with Peano numbers.

<style>
.column {
    float: left;
    width: 50%;
}
.row:after {
    content: "";
    display: table;
    clear: both;
}
</style>
<div class="row">
  <div class="column">
  Haskell

  ```haskell
  data N = Z | S N
  ```
  </div>
  <div class="column">
  Agda
  
  ```agda
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
  ```
  </div>
</div>

(for the rest of this post, when there's two columns, the left is for Haskell,
the right for Agda)

The trees will be balanced one of three possible ways: left-heavy, right-heavy,
or even. We can represent these three cases in a GADT in the case of Haskell,
or an indexed datatype in the case of Agda:

<div class="row">
  <div class="column">
  ```haskell
  data Balance :: N -> N -> N -> Type where
        L :: Balance (S n) n    (S n)
        O :: Balance  n    n     n
        R :: Balance  n   (S n) (S n)
  ```
  </div>
  <div class="column">
  ```agda
  data ⟨_⊔_⟩≡_ : ℕ → ℕ → ℕ → Set where
    ◿  : ∀ {n} → ⟨ suc  n ⊔      n ⟩≡ suc  n
    ▽  : ∀ {n} → ⟨      n ⊔      n ⟩≡      n
    ◺  : ∀ {n} → ⟨      n ⊔ suc  n ⟩≡ suc  n
  ```
  </div>
</div>

Those unfamiliar with Agda might be a little intimidated by the mixfix operator
in the balance definition: we're using it here because the type can be seen of a
proof that:

$$max(x,y) = z$$

Or, using the $\sqcup$ operator:

$$(x \sqcup y) = z$$

We'll use this proof in the tree itself, as we'll need to know the maximum of
the height of a node's two subtrees to find the height of the node. Before we do
that, we'll need a couple helper functions for manipulating the balance:

<div class="row">
  <div class="column">
  ```haskell
  balr :: Balance x y z -> Balance z x z
  balr L = O
  balr O = O
  balr R = L

  ball :: Balance x y z -> Balance y z z
  ball L = R
  ball O = O
  ball R = O
  ```
  </div>
  <div class="column">
  ```agda
  ⃕ : ∀ {x y z} → ⟨ x ⊔ y ⟩≡ z → ⟨ z ⊔ x ⟩≡ z
  ⃕  ◿  = ▽
  ⃕  ▽  = ▽
  ⃕  ◺  = ◿

  ⃔ : ∀ {x y z} → ⟨ x ⊔ y ⟩≡ z → ⟨ y ⊔ z ⟩≡ z
  ⃔  ◿  = ◺
  ⃔  ▽  = ▽
  ⃔  ◺  = ▽
  ```
  </div>
</div>

# Ordering

Along with the verification of the structure of the tree, we will also want to
verify that its contents are ordered correctly. Unfortunately, this property is
a little out of reach for Haskell, but it's 100% doable in Agda. First, we'll
need a way to describe orders on a data type. In Haskell, we might write:

```haskell
class Ord a where
  (==) :: a -> a -> Bool
  (<)  :: a -> a -> Bool
```

That `Bool`{.haskell} throws away any information gained in the comparison,
though: we want to supply a proof with the result of the comparison. First,
equality:

```agda
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
```

This is one of the many ways to describe equality in Agda. It's a  type with
only one constructor, and it can only be constructed when its two arguments are
the same. When we pattern match on the constructor, then, we're given a proof
that whatever things those arguments refer to must be the same.

Next, we need to describe an order. For this, we'll need two types: the empty
type, and the unit type.

```agda
data ⊥ : Set where
data ⊤ : Set where ⟨⟩ : ⊤
```

These are kind of like type-level Bools, with one extra, powerful addition: they
keep their proof after construction. Because `⊥`{.agda} has no constructors, if
someone tells you they're going to give you one, you can be pretty sure they're
lying. How do we use this? Well, first, on the numbers:

```agda
_ℕ<_ : ℕ → ℕ → Set
x     ℕ< zero  = ⊥
zero  ℕ< suc y = ⊤
suc x ℕ< suc y = x ℕ< y
```

Therefore, if we ask for something of type `x ℕ< y`{.agda} (for some `x` and
`y`), we know that it only exists when `x` really is less than `y` (according to
the definition above).

For our actual code, we'll parameterize the whole thing over some abstract key
type. We'll do this using a module (a feature recently added to Haskell, as it
happens). That might look something like this:

```agda
module AVL
  {k r} (Key : Set k)
  {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

  open IsStrictTotalOrder isStrictTotalOrder
```

Now, the trick for the ordering is to keep a proof that two neighboring values
are ordered correctly in the tree at each leaf (as there's a leaf between every
pair of nodes, this is exactly the place you *should* store such a proof). A
problem arises with the extremal leaves in the tree (leftmost and rightmost):
each leaf is missing one neighboring value, so how can it store a proof of
order? The solution is to affix two elements to our key type which we define as
the greatest and least elements of the set.

```agda
infix 5 [_]

data [∙] : Set k where
  ⌊⌋ ⌈⌉ : [∙]
  [_]   : (k : Key) → [∙]

infix 4 _[<]_

_[<]_ : [∙] → [∙] → Set r
⌊⌋     [<] ⌊⌋    = Lift r ⊥
⌊⌋     [<] ⌈⌉    = Lift r ⊤
⌊⌋     [<] [ _ ] = Lift r ⊤
⌈⌉     [<] _     = Lift r ⊥
[ _ ]  [<] ⌊⌋    = Lift r ⊥
[ _ ]  [<] ⌈⌉    = Lift r ⊤
[ x ]  [<] [ y ] = x < y
```

The "lifting" business going on is to deal with Agda's universe levels.

# The Tree Type

After all that, we can get bring back Haskell into the story, and define or tree
types:

<div class="row">
  <div class="column">
  ```haskell

  data Tree :: N
            -> Type
            -> Type
            -> Type where
    Leaf :: Tree Z k v
    Node :: k
         -> v
         -> Balance lh rh h
         -> Tree lh k v
         -> Tree rh k v
         -> Tree (S h) k v
  ```
  </div>
  <div class="column">
  ```agda
  data Tree {v} 
            (V : Key → Set v)
            (l u : [∙]) : ℕ →
            Set (k ⊔ v ⊔ r) where
    leaf  : (l<u : l [<] u) → Tree V l u 0
    node  : ∀  {h lh rh}
               (k : Key)
               (v : V k)
               (bl : ⟨ lh ⊔ rh ⟩≡ h)
               (lk : Tree V l [ k ] lh)
               (ku : Tree V [ k ] u rh) →
               Tree V l u (suc h)
  ```
  </div>
</div>

The two definitions are similar, but have a few obvious differences. The Agda
version stores the ordering proof at the leaves, as well as the bounds as
indices. Its
[*universe*](https://pigworker.wordpress.com/2015/01/09/universe-hierarchies/)
is also different: briefly, universes are related to Russell's paradox. In
Haskell, once you start fiddling around with dependent types, one of the things
you might write is a heterogeneous list:

```haskell
infixr 5 :-
data List xs where
  Nil :: List '[]
  (:-) :: x -> List xs -> List (x : xs)
```

This can quite happily store elements of different types:

```haskell
example :: List [Bool, String, Integer]
example = True :- "true" :- 1 :- Nil
```

It will complain, however, if the types get *too* different:

```haskell
impossible :: List [Bool, String, Maybe]
```

That's because `Maybe`{.haskell} has a different *kind* than the other two.
While the value-level list can have different types, the type-level list is
homogeneous: it's a list of `Type`{.haskell}, but `Maybe`{.haskell} is `Type ->
Type`{.haskell}.

Suppose we wanted to write a list of different kinds, like:

```haskell
strange :: List [Type -> Type, Type, Type -> (Type -> Type)]
```

This type-level list is also homogeneous, but here's the question: what's its
type? Is it still `[Type]`{.haskell}? Or something else entirely?

This is where Haskell and Agda diverge: in Haskell, we say that list has type
`[Type]`{.haskell}, and that's that. However, that implies `Type ::
Type`{.haskell} (as the old extension `TypeInType`{.haskell} implied), which,
from the point of view of correctness, opens the door to Russell's paradox
(we've allowed a set to be a member of itself).

Agda goes another way, saying that `Set`{.agda} (Agda's equivalent for
`Type`{.haskell}) has the type `Set₁`{.agda}, and `Set₁`{.agda} has the type
`Set₂`{.agda}, and so on[^dir]. These different sets are called "universes" and
their numbers "levels". When we write `k ⊔ v ⊔ r`{.agda}, we're saying we want
to take the greatest universe level from those three possible levels: the level
of the key, the value, and the relation, respectively.

[^dir]: My phrasing is maybe a little confusing here. When `Set`{.haskell} "has
    the type" `Set₁`{.agda} it means that `Set`{.haskell} is *in* `Set₁`{.agda},
    not the other way around.

# Rotations

AVL trees maintain their invariants through relatively simple rotations. We'll
start with the right rotation, which fixes an imbalance of two on the left.
Because the size of the tree returned might change, we'll need to wrap it in a datatype:

<div class="row">
  <div class="column">
  ```haskell
  data Inserted :: Type
                -> Type
                -> N
                -> Type where
          Stay :: Tree n k v
               -> Inserted k v n
          Incr :: Tree (S n) k v
               -> Inserted k v n
  ```
  </div>
  <div class="column">
  ```agda
  Inserted  : ∀ {v} 
                (V : Key → Set v)
                (l u : [∙])
                (n : ℕ) →
                Set (k ⊔ v ⊔ r)
  Inserted V l u n =
    ∃[ inc? ] Tree V l u (if inc?
                             then suc n
                             else n)

  pattern 0+ tr = false  , tr
  pattern 1+ tr = true   , tr
  ```
  </div>
</div>

We could actually have the Agda definition be the same as Haskell's, it doesn't
make much difference. I'm mainly using it here to demonstrate dependent pairs in
Agda.

Using this, we can write the type for right-rotation:

<div class="row">
  <div class="column">
  ```haskell
  rotr :: k
       -> v
       -> Tree (S (S rh)) k v
       -> Tree rh k v
       -> Inserted k v (S (S rh))
  ```
  </div>
  <div class="column">
  ```agda
  rotʳ : ∀ {lb ub rh v} {V : Key → Set v}
       → (k : Key)
       → V k
       → Tree V lb [ k ] (suc (suc rh))
       → Tree V [ k ] ub rh
       → Inserted V lb ub (suc (suc rh))
  ```
  </div>
</div>

There are two possible cases, single rotation:

<style>
.tree {
  margin: auto;
  width: 30%;
}
</style>
<div class="tree">
```haskell
   ┌a       ┌a
 ┌y┤       y┤
 │ └b --->  │ ┌b
x┤          └x┤
 └c           └c
```
</div>

<div class="row">
  <div class="column">
  ```haskell
  rotr x xv (Node y yv L a b) c =
    Stay (Node y yv O a (Node x xv O b c))
  rotr x xv (Node y yv O a b) c =
    Incr (Node y yv R a (Node x xv L b c))
  ```
  </div>
  <div class="column">
  ```agda
  rotʳ x xv (node y yv ◿ a b) c =
    0+ (node y yv ▽ a (node x xv ▽  b c))
  rotʳ x xv (node y yv ▽ a b) c =
    1+ (node y yv ◺ a (node x xv ◿  b c))
  ```
  </div>
</div>

And double:

<div class="tree">
```haskell
   ┌a           ┌a
 ┌y┤          ┌y┤
 │ │ ┌b       │ └b
 │ └z┤  ---> z┤
 │   └c       │ ┌c
x┤            └x┤
 └d             └d
```
</div>

<div class="row">
  <div class="column">
  ```haskell
  rotr x xv (Node y yv R a 
              (Node z zv bl b c)) d =
    Stay (Node z zv O 
           (Node y yv (balr bl) a b)
           (Node x xv (ball bl) c d))
  ```
  </div>
  <div class="column">
  ```agda
  rotʳ x xv (node y yv ◺  a
              (node z zv bl b c)) d =
    0+ (node z zv ▽
         (node y yv (⃕ bl) a b)
         (node x xv (⃔ bl) c d))
  ```
  </div>
</div>

I won't bore you with left-rotation: suffice to say, it's the opposite of
right-rotation.

# Insertion

Finally, the main event: insertion. Once the above functions have all been
defined, it's not very difficult, as it happens: by and large, the types guide
you to the right answer. Of course, this is only after we decided to use the
pivotal pragmatism and balance approach.

<div class="row">
  <div class="column">
  ```haskell
  insertWith
      :: Ord k
      => (v -> v -> v)
      -> k
      -> v
      -> Tree h k v
      -> Inserted k v h
  insertWith _ v vc Leaf =
    Incr (Node v vc O Leaf Leaf)
  insertWith f v vc (Node k kc bl tl tr) =
    case compare v k of
      LT ->
        case insertWith f v vc tl of
          Stay tl' ->
            Stay (Node k kc bl tl' tr)
          Incr tl' -> case bl of
            L -> rotr k kc tl' tr
            O -> Incr (Node k kc L tl' tr)
            R -> Stay (Node k kc O tl' tr)
      EQ ->
        Stay (Node v (f vc kc) bl tl tr)
      GT ->
        case insertWith f v vc tr of
          Stay tr' ->
            Stay (Node k kc bl tl tr')
          Incr tr' -> case bl of
            L -> Stay (Node k kc O tl tr')
            O -> Incr (Node k kc R tl tr')
            R -> rotl k kc tl tr'
  ```
  </div>
  <div class="column">
  ```agda
  insert : ∀ {l u h v}
             {V : Key → Set v}
             (k : Key)
         → V k
         → (V k → V k → V k)
         → Tree V l u h
         → l < k < u
         → Inserted V l u h
  insert v vc f (leaf l<u) (l , u) =
    1+ (node v vc ▽ (leaf l) (leaf u))
  insert v vc f (node k kc bl tl tr) prf
    with compare v k
  insert v vc f (node k kc bl tl tr) (l , _)
      | tri< a _ _ with insert v vc f tl (l , a)
  ... | 0+ tl′ = 0+ (node k kc bl tl′ tr)
  ... | 1+ tl′ with bl
  ... | ◿ = rotʳ k kc tl′ tr
  ... | ▽ = 1+ (node k kc  ◿  tl′ tr)
  ... | ◺ = 0+ (node k kc  ▽  tl′ tr)
  insert v vc f (node k kc bl tl tr) _
      | tri≈ _ refl _ =
          0+ (node k (f vc kc) bl tl tr)
  insert v vc f (node k kc bl tl tr) (_ , u)
      | tri> _ _ c with insert v vc f tr (c , u)
  ... | 0+ tr′ = 0+ (node k kc bl tl tr′)
  ... | 1+ tr′ with bl
  ... | ◿ = 0+ (node k kc ▽ tl tr′)
  ... | ▽ = 1+ (node k kc ◺ tl tr′)
  ... | ◺ = rotˡ k kc tl tr′
  ```
  </div>
</div>


# Conclusion

Overall, I found the experience of programming in Agda very enjoyable. The
things I liked surprised me, also:

Editor Support

:   Excellent. I use [spacemacs](http://spacemacs.org), and the whole thing
    worked pretty seamlessly. Proof search and auto was maybe not as powerful as
    Idris', although that might be down to lack of experience (note---as I write
    this, I see you can enable case-splitting in proof search, so it looks like
    it's much more powerful than I thought). In particular, it was much better
    than Haskell's editor support: I have managed, for about five minutes, to
    get case-splitting to work in emacs.
    
    It's worth noting that my experience with Idris is similar: far better
    editor support than Haskell. It's missing lots of extra tools, like linters,
    code formatters, but the tight integration with the compiler was so useful
    it more than made up for it.
    
    Also, I'd implore anyone who's had trouble with emacs before to give
    [spacemacs](http://spacemacs.org) a go. It works well out-of-the-box, and
    it has a system for keybinding discovery that worked really well for me.

Documentation

:   Pretty good, considering. There are some missing parts
    ([rewriting](https://agda.readthedocs.io/en/v2.5.4.1/language/rewriting.html)
    and
    [telescopes](https://agda.readthedocs.io/en/v2.5.4.1/language/telescopes.html)
    are both stubs on the documentation site), but there seemed to be more fully
    worked-out examples available online for different concepts when I needed to
    figure them out.

LaTeX Generation

:   Literate programming is something I have begun to experiment with more
    lately, and Agda's support for it is... admirable? Because LaTeX doesn't
    really support unicode, any attempt to generate unicode-heavy documents
    seems doomed to fail. So while it took a lot of tinkering to get it to work,
    I'm happy that I managed to use Agda for LaTeX generation at all.

Now, the thing about a lot of these complaints/commendations (*especially* with
regards to tooling and personal setups) is that people tend to be pretty bad
about evaluating how difficult finicky tasks like editor setups are. So where I
say Agda has good editor support, it may be that my learning Agda coincided with
me first understanding emacs.

That said, my biggest disappointment was performance, and in particular
irrelevance. Looking back at the definition of the tree type, in the Haskell
version there's no singleton storing the height (the balance type stores all the
information we need), which means that it definitely doesn't exist at runtime.
As I understand it, that implies that the type should be irrelevant in the
equivalent Agda. However, when the proof is marked as irrelevant, everything
works fine, except that missing cases warnings start showing up everywhere. I'm
not sure why this is. Also, the conditions for equality proof erasure are very
unclear to me.

# Further Reading

At the end of these articles, I often see the dreaded phrase "deletion is left
as an exercise to the reader". Not so here! There's a pdf of the Agda code in
this post, with deletion included, [here](/pdfs/AVL.pdf). The repository with
the literate Agda code for that is available
[here](https://github.com/oisdk/agda-avl), and the equivalent for the Haskell
code is [here](https://github.com/oisdk/verified-avl).

# References
