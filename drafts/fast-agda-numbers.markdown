---
title: Writing a Fast Number Implementation in Agda
tags: Agda
---

I've been messing around with some binary number implementations in Agda
recently and I have come across a few tricks to make the representation work
quickly.
In this post I'll go through a few of those tricks, which might be helpful for
other people writing Agda and struggling with performance.

# A Flat Representation

First things first we need to pick a representation for our numbers.
Standard binary numbers are fine and efficient, but defining them properly is a
little tricky because of redundancy, due to the presence of trailing zeroes.
If we have a list of bits, least-significant-bit first, then there are multiple
representations of the same number because we can stick arbitrary zeroes on the
end without changing the semantic value.

In decimal, this is like how "99" and "099" represent the same thing: this is
undesirable for our number representation, because we want semantically equal
numbers to be provably equal as well.

There are a number of ways to get around the problem: towards the fancier end of
the scale, we could construct a quotient type (in cubical Agda) which ignores
trailing zeroes.
This is extremely complex and extremely slow.

Another popular option is to define two types: one for binary numbers which are
possibly zero, and another for binary numbers which end in 1.

```agda
infixr 8 1ᵇ∷_ 0ᵇ∷_
data 𝔹⁺ : Type₀ where
  1ᵇ : 𝔹⁺
  1ᵇ∷_ 0ᵇ∷_ : 𝔹⁺ → 𝔹⁺

data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹
```

While this approach works quite well, and important part of improving Agda's
performance is reducing the complexity of the number type, in terms of
constructors and nesting.
The fact that we have two separate defined types here adds a little programming
complexity, and probably would slow down typechecking a little.

So instead we're going to use the *zeroless* binary numbers.
They look like the following:

```agda
infixr 8 1ᵇ_ 2ᵇ_
data 𝔹 : Type₀ where
  0ᵇ : 𝔹
  1ᵇ_ 2ᵇ_ : 𝔹 → 𝔹
```

This type does indeed have a bijection with ℕ, with the following semantics:

```agda
⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 1ᵇ xs ⇓⟧ = 1 + ⟦ xs ⇓⟧ * 2
⟦ 2ᵇ xs ⇓⟧ = 2 + ⟦ xs ⇓⟧ * 2
```


But it's a single recursive type, with no parameters or nesting whatsoever.
That helps performance quite a bit, which is why we *didn't* define the type
using lists and booleans:

```agda
𝔹 : Type₀
𝔹 = List Bool

infixr 8 1ᵇ_ 2ᵇ_
pattern 0ᵇ = []
pattern 1ᵇ_ xs = false ∷ xs
pattern 2ᵇ_ xs = true  ∷ xs
```

In testing, the list-of-bools approach was significantly slower than the flat
datatype approach.

The single, flat type can make some of the subsequent functions inelegant, and
it's often annoying that we can't use common abstractions like `foldr`, but
that's the price we pay.
Also, often the simpler code is easier to read, if a little repetitive.

The problem with performance in Agda is that we're optimising for an
interpreter, not a compiler: we want these numbers to be fast for
*typechecking*.
A lot of what makes Haskell code fast is that common abstractions get optimised
away: that just doesn't happen for interpreted code (usually).
As a result, we have to write things a little differently.

# Conversion

Next we will define the isomorphism between 𝔹 and ℕ.
We've already defined how to convert to ℕ: it's important that we use the
built-in `+` and `*` functions here, since they actually call out to Haskell
functions on `Integer` which are much faster than anything we could define.

Part of the puzzle for defining the conversion functions is to figure out *how*
to use the built-in functions Agda gives to us in a way that still makes the
expressions easy to write proofs about.
For instance, the second and third clauses of the `⟦_⇓⟧` are as follows:

```agda
⟦ 1ᵇ xs ⇓⟧ = 1 + ⟦ xs ⇓⟧ * 2
⟦ 2ᵇ xs ⇓⟧ = 2 + ⟦ xs ⇓⟧ * 2
```

There are a number of other ways we could have written this:

```agda
-- Swapping the arguments to _*_, yielding something
-- arguably more natural:
⟦ 1ᵇ xs ⇓⟧ = 1 + 2 * ⟦ xs ⇓⟧
⟦ 2ᵇ xs ⇓⟧ = 2 + 2 * ⟦ xs ⇓⟧

-- The following actually looks the *simplest* to write proofs
-- about:
⟦ 1ᵇ xs ⇓⟧ = let rest = ⟦ xs ⇓⟧ in 1 + (rest + rest)
⟦ 2ᵇ xs ⇓⟧ = let rest = ⟦ xs ⇓⟧ in 2 + (rest + rest)
```

But all of these have slightly trickier associated proofs.
The key proof associated with converting *to* ℕ is the following:

```agda
inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc 0ᵇ     = refl
inc-suc (1ᵇ x) = refl
inc-suc (2ᵇ x) = cong (λ rest → 1 + (rest * 2)) (inc-suc x)
```

The simplicity of this comes directly from the definitions we used.
There may well be a simpler proof out there which has some different order of
arguments, but this is the best I've found so far.

Conversion from ℕ is quite simple:

```agda
inc : 𝔹 → 𝔹
inc 0ᵇ      = 1ᵇ 0ᵇ
inc (1ᵇ xs) = 2ᵇ xs
inc (2ᵇ xs) = 1ᵇ inc xs

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
```

The full proof of isomorphism is very short indeed:

<details>
<summary>Proof of isomorphism</summary>

```agda
inc-2*-1ᵇ : ∀ n → inc ⟦ n * 2 ⇑⟧ ≡ 1ᵇ ⟦ n ⇑⟧
inc-2*-1ᵇ zero    = refl
inc-2*-1ᵇ (suc n) = cong inc (cong inc (inc-2*-1ᵇ n))

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero    = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ; cong suc (𝔹-rightInv x)

𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹-leftInv 0ᵇ = refl
𝔹-leftInv (1ᵇ x) =           inc-2*-1ᵇ ⟦ x ⇓⟧  ; cong 1ᵇ_ (𝔹-leftInv x)
𝔹-leftInv (2ᵇ x) = cong inc (inc-2*-1ᵇ ⟦ x ⇓⟧) ; cong 2ᵇ_ (𝔹-leftInv x)

𝔹⇔ℕ : 𝔹 ⇔ ℕ
𝔹⇔ℕ .fun = ⟦_⇓⟧
𝔹⇔ℕ .inv = ⟦_⇑⟧
𝔹⇔ℕ .rightInv = 𝔹-rightInv
𝔹⇔ℕ .leftInv  = 𝔹-leftInv
```
</details>

# Strictness

Our function above for converting from ℕ could use some improvement.
It uses $\mathcal{O}(n)$ time, and $\mathcal{O}(n)$ space: we'll fix the latter
of those in this section.

The conversion we have defined above evaluates a little like this:

```agda
   ⟦ 5 ⇑⟧
~> ⟦ suc (suc (suc (suc (suc zero)))) ⇑⟧
~> inc (inc (inc (inc (inc 0ᵇ))))
~> 1ᵇ 2ᵇ 0ᵇ
```

This is in fact a classic space leak, almost the same as the kind you key from
using a lazy `foldl` incorrectly in Haskell.
Because the `inc` function is strict, we *have* to build up the long chain of
calls to `inc` before we can do any reduction.
A better way to go is to build up an accumulator as we go, which can reduce on
each step of the computation.

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦_⇑⟧ = go 0ᵇ
  where
  go : 𝔹 → ℕ → 𝔹
  go a zero    = a
  go a (suc n) = go (inc a) n
```

Unfortunately, laziness will preserve the space leak even in the above function.
We need to force the accumulator in order to keep the function constant space.

Strictness in Agda is strange for a few reasons.
First of all, formally speaking, Agda programs can be interpreted either
strictly *or* lazily: in contrast to Haskell, where forcing a given computation
can give different results (modulo `unsafePerformIO`, the different results are
only `⊥` or whatever the value is), all Agda programs must evaluate to the same
value regardless of the evaluation method used (with the exception of
coinductive types, which have to be evaluated lazily, although).

Secondly there's the question of how laziness interacts with *proofs*.
As an example, consider the following implementation of addition:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
```

Both clauses hold as equalities definitionally.
In other words, you will never have to prove that `0 + x = x`, as the
typechecker knows it implicitly.

Some other equations---which are true---don't hold definitionally.
`x + 0 = x` is a common example.
Now this equality is true, but you have to inspect `x` in its entirety to make
the typechecker realise it.
So if we have a concrete `x`, say 5, then the typechecker will have no issue
with discharging the proof obligation automatically.

```agda
x : ℕ
x = 5

_ : x + 0 ≡ x
_ = refl
```

Strictness causes a similar thing: equations cease to hold definitionally until
we inspect some other values.
However, unlike the `x + 0` example, the value we need to inspect is the
*output*.
Here's a redefined strict definition of `+`:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc $! (n + m)
```

`$!` is the strict application operator: it forces the right-hand-side (to weak
head normal form) before applying the function on the left.
Now, equalities like `suc n + m ≡ suc (n + m)` *won't* hold definitionally.
But, if we can inspect `n` and `m`, then it will:

```agda
_ : suc 5 + 5 ≡ suc (5 + 5)
_ = refl
```

At first, the lack of these definitional equalities bothered me a little: it
seemed like a wart in strictness in Agda, and put me off of it for a bit.
Of course, the lack of definitional equalities is the *point* of the strictness. 
We *want* to force the evaluation of the argument before comparing it for
equality.
On top of that, Agda actually does give us a primitive which says basically the
following: 

```agda
∀ f x → f $! x ≡ f x
```

Which means that in proofs we can remove the strictness, but still have the
strictness behaviour when using the function normally.

So, finally we can write a strict version of our conversion function.
We'll use this cute function to emulate bang patterns from Haskell:

```agda
infixr 0 let-bang
let-bang : {A : Type a} {B : A → Type b} → ∀ x → (∀ x → B x) → B x
let-bang = primForce
{-# INLINE let-bang #-}

syntax let-bang v (λ x → e) = let! x =! v in! e
```

This transforms our conversion function into the following:

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦_⇑⟧ = go 0ᵇ
  where
  go : 𝔹 → ℕ → 𝔹
  go a zero    = a
  go a (suc n) = let! a′ =! inc′ a in! go a′ n
```

(This isn't actually complete: you would have to write a strict version of `inc`
as well)

Actually, it is a little cleaner to recognise the more general pattern here, and
define the functions as strict folds on `ℕ`:

```agda
foldr-ℕ : (A → A) → A → ℕ → A
foldr-ℕ f b zero    = b
foldr-ℕ f b (suc n) = f (foldr-ℕ f b n)

foldl-ℕ-go : (A → A) → ℕ → A → A
foldl-ℕ-go f zero    x = x
foldl-ℕ-go f (suc n) x = foldl-ℕ-go f n $! f x

foldl-ℕ : (A → A) → A → ℕ → A
foldl-ℕ f x n = foldl-ℕ-go f n $! x
```

Then we can prove that both the strict and lazy forms of these functions are
equivalent:

```agda
f-comm : ∀ (f : A → A) x n → f (foldr-ℕ f x n) ≡ foldr-ℕ f (f x) n
f-comm f x zero    i = f x
f-comm f x (suc n) i = f (f-comm f x n i)

foldl-ℕ-foldr : ∀ f (x : A) n → foldr-ℕ f x n ≡ foldl-ℕ f x n
foldl-ℕ-foldr f x zero    = sym ($!-≡ (foldl-ℕ-go f zero) x)
foldl-ℕ-foldr f x (suc n) = f-comm f x n 
                          ; foldl-ℕ-foldr f (f x) n 
                          ; sym ($!-≡ (foldl-ℕ-go f (suc n)) x)
```

This means we can define our conversion from the Peano numbers in the strict
form, but prove things about the lazy form.

# Termination

There is a way to convert from `ℕ` that is faster still: we could rely on Agda's
built-in `div` and `mod` functions to avoid the `inc` step altogether.

```agda
⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ =
  if even n
  then 1ᵇ ⟦ n ÷ 2 ⇑⟧
  else 2ᵇ ⟦ n ÷ 2 ⇑⟧
```

This is by far and away the fastest method for converting from ℕ.
Unfortunately, it doesn't pass the termination checker: Agda can't obviously
tell that `n ÷ 2` is smaller than `suc n`.

At first, this seemed to me like a perfect case for using well-founded
recursion.
This is a heavy-duty, generic way to prove termination in more complex cases.
You basically prove that a particular relation (like `_<_` on ℕ) is well
founded, and then you pass a structure along with the recursive calls that shows
the termination checker the recursion is indeed bounded.
For the above function, that looks like this:

```agda
⟦_⇑⟧⟨_⟩ : ∀ n → Acc _<_ n → 𝔹
⟦ zero  ⇑⟧⟨     wf ⟩ = 0ᵇ
⟦ suc n ⇑⟧⟨ acc wf ⟩ =
  if even n
  then 1ᵇ ⟦ n ÷ 2 ⇑⟧⟨ wf (n ÷ 2) (s≤s (div2≤ n)) ⟩
  else 2ᵇ ⟦ n ÷ 2 ⇑⟧⟨ wf (n ÷ 2) (s≤s (div2≤ n)) ⟩

⟦_⇑⟧ : ℕ → 𝔹
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ ≤-wellFounded n ⟩
```

Unfortunately, this version is horrifically slow, taking several minutes to
evaluate `⟦ 5000 ⇑⟧`.

There's one trick we can use here, though, that will get us the desired
performance without sacrificing provable termination.
We will pass the number itself as the bounds for recursion.

```agda
⟦_⇑⟧⟨_⟩ : ℕ → ℕ → 𝔹
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  if even n
    then 1ᵇ ⟦ n ÷ 2 ⇑⟧⟨ w ⟩
    else 2ᵇ ⟦ n ÷ 2 ⇑⟧⟨ w ⟩
⟦ zero  ⇑⟧⟨ _     ⟩ = 0ᵇ
⟦ suc _ ⇑⟧⟨ zero  ⟩ = 0ᵇ -- will not happen

⟦_⇑⟧ : ℕ → 𝔹
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ n ⟩
```

This differs from the usual notion of well-founded recursion in that the
structure we pass to show that the algorithm is structurally terminating isn't
a proposition: it can be more than one value, *and* it can affect the output.
This has to be accounted for in the proofs: we need to pass a proof that the
number being recursed on is always smaller than the termination helper so that
the output is correct.

```agda
fast-correct-helper : ∀ n w → n ≤ w → ⟦ n ⇑⟧⟨ w ⟩ ≡ ⟦ n ⇑⟧
```

The `⟦ n ⇑⟧` on the right there is our old slow conversion.
With this helper we can prove that the fast conversion and slow produce the same
output.

# Operations

## Addition

Now we need to encode the different desired operations on the binary numbers.
Addition is first: we can write a naive version of this function by just
expanding the definition of addition and definition of the binary numbers.

```
0           + y           = y

x           + 0           = x

(1 + 2 * x) + (1 + 2 * y) = 2 + 2 * (x + y)

(1 + 2 * x) + (2 + 2 * y) = 3 + 2 * (x + y)
                          = 1 + (2 + 2 * (x + y))

(2 + 2 * x) + (1 + 2 * y) = 3 + 2 * (x + y)
                          = 1 + (2 + 2 * (x + y))

(2 + 2 * x) + (2 + 2 * y) = 4 + 2 * (x + y)
                          = 2 + 2 * (1 + x + y)
```

Translated into Agda the above looks like the following:

```agda
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
xs    + 0ᵇ    = xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = inc (2ᵇ (xs + ys))
2ᵇ xs + 1ᵇ ys = inc (2ᵇ (xs + ys))
2ᵇ xs + 2ᵇ ys = 2ᵇ inc (xs + ys)
```

Unfortunately this is nowhere near as efficient as it could be: we're calling
`inc` a bunch of times on the output of the recursive call, when we should be
using carrying to do the whole thing in one pass.
That does make the function a lot longer, but it is much faster:

<details>
<summary>Full Addition Implementation</summary>

```agda
add₁ : 𝔹 → 𝔹 → 𝔹
add₂ : 𝔹 → 𝔹 → 𝔹

add₁ 0ᵇ      ys      = inc ys
add₁ (1ᵇ xs) 0ᵇ      = 2ᵇ xs
add₁ (2ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ add₁ xs ys
add₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys

add₂ 0ᵇ      0ᵇ      = 2ᵇ 0ᵇ
add₂ 0ᵇ      (1ᵇ ys) = 1ᵇ inc ys
add₂ 0ᵇ      (2ᵇ ys) = 2ᵇ inc ys
add₂ (1ᵇ xs) 0ᵇ      = 1ᵇ inc xs
add₂ (2ᵇ xs) 0ᵇ      = 2ᵇ inc xs
add₂ (1ᵇ xs) (1ᵇ ys) = 2ᵇ add₁ xs ys
add₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ add₂ xs ys
add₂ (2ᵇ xs) (2ᵇ ys) = 2ᵇ add₂ xs ys

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
1ᵇ xs + 0ᵇ    = 1ᵇ xs
2ᵇ xs + 0ᵇ    = 2ᵇ xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 1ᵇ ys = 1ᵇ add₁ xs ys
2ᵇ xs + 2ᵇ ys = 2ᵇ add₁ xs ys
```
</details>

## Multiplication

Multiplication of binary numbers is actually one of the most well-studied
algorithms out there: the standard encoding will get you an $\mathcal{O}(n^2)$
(where $n$ is the number of bits) algorithm, but there are actually some
reasonably easy-to-implement algorithms (Karatsuba multiplication being the most
prominent) that can improve on that bound.
In fact, in 2019 an $\mathcal{O}(n \log n)$ algorithm was discovered: whether or
not such an algorithm existed was an important open question in computer
science.

Now, Karatsuba multiplication is actually a relatively simple algorithm, but it
only actually gets a speedup when the numbers being multiplied have much more
than 300 bits.
For our purposes (a general-purpose number type to replace the peano numbers in
Agda), we're probably better off with just the standard long multiplication.

```agda
double : 𝔹 → 𝔹
double 0ᵇ = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys + double (ys * xs)
2ᵇ xs * ys = double (ys + ys * xs)
```

One thing that is interesting about the above implementation is that it swaps
the order of arguments to `*` in the recursive call: this reduces the usual
left-bias of lazy operations.
It means that both operands are explored at a similar rate.
In performance tests it yields a modest speedup.

## Subtraction

Subtraction is by far the trickiest of the operations I'm presenting here.
Like addition, we could write a naive and obviously correct implementation, but
in order for the function to have the correct time complexity we need to write
something much more involved.

The problem with subtraction is that we don't know what the output is going to
look like until we've seen the entirety of at least one of the inputs: so the
function can't have the nice linear pattern that addition has.
(at least I think it can't: if anyone can write a simple implementation of
subtraction on the zeroless binary numbers which uses carry bits or something I
would love to see it)

So what we're left with is a function which needs to build up a chain of extra
function calls as it descends into the numbers it's inspecting.
Instead of encoding these as actual functions, we can defunctionalise them,
encoding them as a second binary number.
It's a little complex to explain, so here's what the solution looks like:

<details>
<summary>Subtraction</summary>

```agda
dec′ : 𝔹 → 𝔹
dec : 𝔹 → 𝔹

dec′ 0ᵇ = 0ᵇ
dec′ (1ᵇ xs) = 2ᵇ dec′ xs
dec′ (2ᵇ xs) = 2ᵇ 1ᵇ xs

dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = dec′ xs

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

push : 𝔹 → 𝔹 → 𝔹
push 0ᵇ     xs      = xs
push (2ᵇ t) xs      = push t (2ᵇ xs)
push (1ᵇ t) 0ᵇ      = push t 0ᵇ
push (1ᵇ t) (1ᵇ xs) = push t (1ᵇ xs)
push (1ᵇ t) (2ᵇ xs) = push t (2ᵇ 1ᵇ xs)

sub₄ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹
sub₃ : ℕ → 𝔹 → 𝔹 → 𝔹 → 𝔹

sub₄ n t 0ᵇ         ys      = 0ᵇ
sub₄ n t (1ᵇ xs)    (1ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    (2ᵇ ys) = sub₄ n (1ᵇ t) xs ys
sub₄ n t (1ᵇ xs)    0ᵇ      = ones n (push (1ᵇ t) (dec′ xs))
sub₄ n t (2ᵇ xs)    (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₄ n t (2ᵇ xs)    0ᵇ      = ones n (push (2ᵇ t) (dec′ xs))

sub₃ n t 0ᵇ      0ᵇ      = ones n (push t 0ᵇ)
sub₃ n t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₃ n t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₃ n t (1ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ dec′ xs))
sub₃ n t (2ᵇ xs) 0ᵇ      = ones n (push t (2ᵇ 1ᵇ xs))
sub₃ n t (1ᵇ xs) (1ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (2ᵇ ys) = sub₃ n (1ᵇ t) xs ys
sub₃ n t (1ᵇ xs) (2ᵇ ys) = sub₄ n (2ᵇ t) xs ys
sub₃ n t (2ᵇ xs) (1ᵇ ys) = sub₃ n (2ᵇ t) xs ys

sub₂ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₂ t 0ᵇ      ys      = 0ᵇ
sub₂ t (1ᵇ xs) 0ᵇ      = ones t (dec′ xs)
sub₂ t (2ᵇ xs) 0ᵇ      = ones t (1ᵇ xs)
sub₂ t (1ᵇ xs) (1ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (2ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys
sub₂ t (1ᵇ xs) (2ᵇ ys) = sub₄ t 0ᵇ xs ys
sub₂ t (2ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys

sub₁ : ℕ → 𝔹 → 𝔹 → 𝔹
sub₁ t xs      0ᵇ      = ones t xs
sub₁ t 0ᵇ      (1ᵇ ys) = 0ᵇ
sub₁ t 0ᵇ      (2ᵇ ys) = 0ᵇ
sub₁ t (1ᵇ xs) (1ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (2ᵇ ys) = sub₃ t 0ᵇ xs ys
sub₁ t (2ᵇ xs) (1ᵇ ys) = sub₁ (suc t) xs ys
sub₁ t (1ᵇ xs) (2ᵇ ys) = sub₂ (suc t) xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
_-_ = sub₁ zero
```
</details>

# Order

I've described how to do ordering on binary numbers in Agda before, but I'll
show it again here.
The key is to define `_≤_` and `_<_` at the same time, and to use booleans
aggressively.
Indexed data types are extremely powerful, but they don't actually work very
well for this particular use case.
Here's the code:

```agda
infix 4 _≲ᴮ_&_
_≲ᴮ_&_ : 𝔹 → 𝔹 → Bool → Bool
0ᵇ    ≲ᴮ ys    & true  = true
0ᵇ    ≲ᴮ 0ᵇ    & false = false
0ᵇ    ≲ᴮ 1ᵇ ys & false = true
0ᵇ    ≲ᴮ 2ᵇ ys & false = true
1ᵇ xs ≲ᴮ 0ᵇ    & s     = false
1ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & s
1ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & true
2ᵇ xs ≲ᴮ 0ᵇ    & s     = false
2ᵇ xs ≲ᴮ 1ᵇ ys & s     = xs ≲ᴮ ys & false
2ᵇ xs ≲ᴮ 2ᵇ ys & s     = xs ≲ᴮ ys & s

infix 4 _≤ᴮ_ _<ᴮ_
_≤ᴮ_ : 𝔹 → 𝔹 → Bool
xs ≤ᴮ ys = xs ≲ᴮ ys & true

_<ᴮ_ : 𝔹 → 𝔹 → Bool
xs <ᴮ ys = xs ≲ᴮ ys & false

infix 4 _≤_ _<_
_≤_ : 𝔹 → 𝔹 → Type₀
xs ≤ ys = T (xs ≤ᴮ ys)

_<_ : 𝔹 → 𝔹 → Type₀
xs < ys = T (xs <ᴮ ys)
```
