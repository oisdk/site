---
title: Terminating Tricky Traversals
tags: Agda, Haskell
series: Breadth-First Traversals
bibliography: Breadth First Traversals.bib
---

<details>
<summary>
Imports
</summary>


<pre class="Agda"><a id="192" class="Symbol">{-#</a> <a id="196" class="Keyword">OPTIONS</a> <a id="204" class="Pragma">--cubical</a> <a id="214" class="Pragma">--sized-types</a> <a id="228" class="Symbol">#-}</a>

<a id="233" class="Keyword">module</a> <a id="240" href="" class="Module">Post</a> <a id="245" class="Keyword">where</a>

<a id="252" class="Keyword">open</a> <a id="257" class="Keyword">import</a> <a id="264" href="../code/terminating-tricky-traversals/Post.Prelude.html" class="Module">../code/terminating-tricky-traversals/Post.Prelude</a>
</pre>
</details>


Just a short one today.
I'm going to look at a couple of algorithms for breadth-first traversals with
complex termination proofs.

# Breadth-First Graph Traversal

In a previous post I talked about breadth-first traversals over graphs, and the
difficulties that cycles cause.
Graphs are especially tricky to work with in a purely functional language,
because so many of the basic algorithms are described in explicitly mututing
terms (i.e. "mark off a node as you see it"), with no obvious immutable
translation.
The following is the last algoirthm I came up with:

```haskell
bfs :: Ord a => (a -> [a]) -> a -> [[a]]
bfs g r = takeWhile (not.null) (map fst (fix (f r . push)))
  where
    push xs = ([],Set.empty) : [ ([],seen) | (_,seen) <- xs ]
    f x q@((l,s):qs)
      | Set.member x s = q
      | otherwise = (x:l, Set.insert x s) : foldr f qs (g x)
```

As difficult as it is to work with graphs in a pure functional language, it's
even *more* difficult to work in a *total* language, like Agda.
Looking at the above function, there are several bits that we can see right off
the bat won't translate over easily.
Let's start with `fix`.

We shouldn't expect to be able to write `fix` in Agda as-is.
Just look at its Haskell implementation:

```haskell
fix :: (a -> a) -> a
fix f = f (fix f)
```

It's obviously non total!

(this is actually a non-memoizing version of `fix`, which is different from the
[usual
one](https://stackoverflow.com/questions/37366222/why-is-this-version-of-fix-more-efficient-in-haskell/37366374))

We can write a function *like* `fix`, though, using coinduction and sized types.

<pre class="Agda"><a id="1890" class="Keyword">record</a> <a id="Thunk"></a><a id="1897" href="#1897" class="Record">Thunk</a> <a id="1903" class="Symbol">(</a><a id="1904" href="#1904" class="Bound">A</a> <a id="1906" class="Symbol">:</a> <a id="1908" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#179" class="Postulate">Size</a> <a id="1913" class="Symbol">→</a> <a id="1915" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="1920" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="1921" class="Symbol">)</a> <a id="1923" class="Symbol">(</a><a id="1924" href="#1924" class="Bound">i</a> <a id="1926" class="Symbol">:</a> <a id="1928" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#179" class="Postulate">Size</a><a id="1932" class="Symbol">)</a> <a id="1934" class="Symbol">:</a> <a id="1936" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="1941" href="#1920" class="Bound">a</a> <a id="1943" class="Keyword">where</a>
  <a id="1951" class="Keyword">coinductive</a>
  <a id="1965" class="Keyword">field</a> <a id="Thunk.force"></a><a id="1971" href="#1971" class="Field">force</a> <a id="1977" class="Symbol">:</a> <a id="1979" class="Symbol">∀</a> <a id="1981" class="Symbol">{</a><a id="1982" href="#1982" class="Bound">j</a> <a id="1984" class="Symbol">:</a> <a id="1986" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#211" class="Postulate Operator">Size&lt;</a> <a id="1992" href="#1924" class="Bound">i</a><a id="1993" class="Symbol">}</a> <a id="1995" class="Symbol">→</a> <a id="1997" href="#1904" class="Bound">A</a> <a id="1999" href="#1982" class="Bound">j</a>
<a id="2001" class="Keyword">open</a> <a id="2006" href="#1897" class="Module">Thunk</a> <a id="2012" class="Keyword">public</a>

<a id="fix"></a><a id="2020" href="#2020" class="Function">fix</a> <a id="2024" class="Symbol">:</a> <a id="2026" class="Symbol">(</a><a id="2027" href="#2027" class="Bound">A</a> <a id="2029" class="Symbol">:</a> <a id="2031" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#179" class="Postulate">Size</a> <a id="2036" class="Symbol">→</a> <a id="2038" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="2043" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="2044" class="Symbol">)</a> <a id="2046" class="Symbol">→</a> <a id="2048" class="Symbol">(∀</a> <a id="2051" class="Symbol">{</a><a id="2052" href="#2052" class="Bound">i</a><a id="2053" class="Symbol">}</a> <a id="2055" class="Symbol">→</a> <a id="2057" href="#1897" class="Record">Thunk</a> <a id="2063" href="#2027" class="Bound">A</a> <a id="2065" href="#2052" class="Bound">i</a> <a id="2067" class="Symbol">→</a> <a id="2069" href="#2027" class="Bound">A</a> <a id="2071" href="#2052" class="Bound">i</a><a id="2072" class="Symbol">)</a> <a id="2074" class="Symbol">→</a> <a id="2076" class="Symbol">∀</a> <a id="2078" class="Symbol">{</a><a id="2079" href="#2079" class="Bound">j</a><a id="2080" class="Symbol">}</a> <a id="2082" class="Symbol">→</a> <a id="2084" href="#2027" class="Bound">A</a> <a id="2086" href="#2079" class="Bound">j</a>
<a id="2088" href="#2020" class="Function">fix</a> <a id="2092" href="#2092" class="Bound">A</a> <a id="2094" href="#2094" class="Bound">f</a> <a id="2096" class="Symbol">=</a> <a id="2098" href="#2094" class="Bound">f</a> <a id="2100" class="Symbol">λ</a> <a id="2102" class="Keyword">where</a> <a id="2108" class="Symbol">.</a><a id="2109" href="#1971" class="Field">force</a> <a id="2115" class="Symbol">→</a> <a id="2117" href="#2020" class="Function">fix</a> <a id="2121" href="#2092" class="Bound">A</a> <a id="2123" href="#2094" class="Bound">f</a>
</pre>
Coinductive types are the dual to inductive types.
Totality-wise, a coinductive type must be "productive"; i.e. a coinductive list
can be infinitely long, but it must be provably able to evaluate to a
constructor (cons or nil) in finite time.

Sized types also help us out here: they're quite subtle, and a little finicky to
use occasionally, but they are invaluable when it comes to proving termination
or productivity of complex (especially higher-order) functions.
The canonical example is mapping over the following tree type:

<pre class="Agda"><a id="2670" class="Keyword">module</a> <a id="NonTerminating"></a><a id="2677" href="#2677" class="Module">NonTerminating</a> <a id="2692" class="Keyword">where</a>
  <a id="2700" class="Keyword">data</a> <a id="NonTerminating.Tree"></a><a id="2705" href="#2705" class="Datatype">Tree</a> <a id="2710" class="Symbol">(</a><a id="2711" href="#2711" class="Bound">A</a> <a id="2713" class="Symbol">:</a> <a id="2715" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="2720" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="2721" class="Symbol">)</a> <a id="2723" class="Symbol">:</a> <a id="2725" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="2730" href="#2720" class="Bound">a</a> <a id="2732" class="Keyword">where</a>
    <a id="NonTerminating.Tree._&amp;_"></a><a id="2742" href="#2742" class="InductiveConstructor Operator">_&amp;_</a> <a id="2746" class="Symbol">:</a> <a id="2748" href="#2711" class="Bound">A</a> <a id="2750" class="Symbol">→</a> <a id="2752" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="2757" class="Symbol">(</a><a id="2758" href="#2705" class="Datatype">Tree</a> <a id="2763" href="#2711" class="Bound">A</a><a id="2764" class="Symbol">)</a> <a id="2766" class="Symbol">→</a> <a id="2768" href="#2705" class="Datatype">Tree</a> <a id="2773" href="#2711" class="Bound">A</a>

  <a id="2778" class="Symbol">{-#</a> <a id="2782" class="Keyword">TERMINATING</a> <a id="2794" class="Symbol">#-}</a>
  <a id="NonTerminating.mapTree"></a><a id="2800" href="#2800" class="Function">mapTree</a> <a id="2808" class="Symbol">:</a> <a id="2810" class="Symbol">(</a><a id="2811" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="2813" class="Symbol">→</a> <a id="2815" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="2816" class="Symbol">)</a> <a id="2818" class="Symbol">→</a> <a id="2820" href="#2705" class="Datatype">Tree</a> <a id="2825" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="2827" class="Symbol">→</a> <a id="2829" href="#2705" class="Datatype">Tree</a> <a id="2834" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a>
  <a id="2838" href="#2800" class="Function">mapTree</a> <a id="2846" href="#2846" class="Bound">f</a> <a id="2848" class="Symbol">(</a><a id="2849" href="#2849" class="Bound">x</a> <a id="2851" href="#2742" class="InductiveConstructor Operator">&amp;</a> <a id="2853" href="#2853" class="Bound">xs</a><a id="2855" class="Symbol">)</a> <a id="2857" class="Symbol">=</a> <a id="2859" href="#2846" class="Bound">f</a> <a id="2861" href="#2849" class="Bound">x</a> <a id="2863" href="#2742" class="InductiveConstructor Operator">&amp;</a> <a id="2865" href="../code/terminating-tricky-traversals/Post.Prelude.html#678" class="Function">map</a> <a id="2869" class="Symbol">(</a><a id="2870" href="#2800" class="Function">mapTree</a> <a id="2878" href="#2846" class="Bound">f</a><a id="2879" class="Symbol">)</a> <a id="2881" href="#2853" class="Bound">xs</a>
</pre>
The compiler can't tell that the recursive call in the `mapTree` function will
only be called on subnodes of the argument: it can't tell that it's structurally
recursive, in other words.
Annoyingly, we can fix the problem by inlining `map`.

<pre class="Agda">  <a id="3141" class="Keyword">mutual</a>
    <a id="NonTerminating.mapTree′"></a><a id="3152" href="#3152" class="Function">mapTree′</a> <a id="3161" class="Symbol">:</a> <a id="3163" class="Symbol">(</a><a id="3164" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="3166" class="Symbol">→</a> <a id="3168" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="3169" class="Symbol">)</a> <a id="3171" class="Symbol">→</a> <a id="3173" href="#2705" class="Datatype">Tree</a> <a id="3178" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="3180" class="Symbol">→</a> <a id="3182" href="#2705" class="Datatype">Tree</a> <a id="3187" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a>
    <a id="3193" href="#3152" class="Function">mapTree′</a> <a id="3202" href="#3202" class="Bound">f</a> <a id="3204" class="Symbol">(</a><a id="3205" href="#3205" class="Bound">x</a> <a id="3207" href="#2742" class="InductiveConstructor Operator">&amp;</a> <a id="3209" href="#3209" class="Bound">xs</a><a id="3211" class="Symbol">)</a> <a id="3213" class="Symbol">=</a> <a id="3215" href="#3202" class="Bound">f</a> <a id="3217" href="#3205" class="Bound">x</a> <a id="3219" href="#2742" class="InductiveConstructor Operator">&amp;</a> <a id="3221" href="#3241" class="Function">mapForest</a> <a id="3231" href="#3202" class="Bound">f</a> <a id="3233" href="#3209" class="Bound">xs</a>

    <a id="NonTerminating.mapForest"></a><a id="3241" href="#3241" class="Function">mapForest</a> <a id="3251" class="Symbol">:</a> <a id="3253" class="Symbol">(</a><a id="3254" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="3256" class="Symbol">→</a> <a id="3258" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="3259" class="Symbol">)</a> <a id="3261" class="Symbol">→</a> <a id="3263" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="3268" class="Symbol">(</a><a id="3269" href="#2705" class="Datatype">Tree</a> <a id="3274" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a><a id="3275" class="Symbol">)</a> <a id="3277" class="Symbol">→</a> <a id="3279" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="3284" class="Symbol">(</a><a id="3285" href="#2705" class="Datatype">Tree</a> <a id="3290" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="3291" class="Symbol">)</a>
    <a id="3297" href="#3241" class="Function">mapForest</a> <a id="3307" href="#3307" class="Bound">f</a> <a id="3309" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a> <a id="3312" class="Symbol">=</a> <a id="3314" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a>
    <a id="3321" href="#3241" class="Function">mapForest</a> <a id="3331" href="#3331" class="Bound">f</a> <a id="3333" class="Symbol">(</a><a id="3334" href="#3334" class="Bound">x</a> <a id="3336" href="../code/terminating-tricky-traversals/Post.Prelude.html#556" class="InductiveConstructor Operator">∷</a> <a id="3338" href="#3338" class="Bound">xs</a><a id="3340" class="Symbol">)</a> <a id="3342" class="Symbol">=</a> <a id="3344" href="#3152" class="Function">mapTree′</a> <a id="3353" href="#3331" class="Bound">f</a> <a id="3355" href="#3334" class="Bound">x</a> <a id="3357" href="../code/terminating-tricky-traversals/Post.Prelude.html#556" class="InductiveConstructor Operator">∷</a> <a id="3359" href="#3241" class="Function">mapForest</a> <a id="3369" href="#3331" class="Bound">f</a> <a id="3371" href="#3338" class="Bound">xs</a>
</pre>
The other solution is to give the tree a size parameter.
This way, all submodes of a given tree will have smaller sizes, which will give
the compiler a finite descending chain condition it can use to prove termination.

<pre class="Agda"><a id="3606" class="Keyword">data</a> <a id="Tree"></a><a id="3611" href="#3611" class="Datatype">Tree</a> <a id="3616" class="Symbol">(</a><a id="3617" href="#3617" class="Bound">A</a> <a id="3619" class="Symbol">:</a> <a id="3621" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="3626" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="3627" class="Symbol">)</a> <a id="3629" class="Symbol">(</a><a id="3630" href="#3630" class="Bound">i</a> <a id="3632" class="Symbol">:</a> <a id="3634" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#179" class="Postulate">Size</a><a id="3638" class="Symbol">)</a> <a id="3640" class="Symbol">:</a> <a id="3642" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="3647" href="#3626" class="Bound">a</a> <a id="3649" class="Keyword">where</a>
  <a id="Tree._&amp;_"></a><a id="3657" href="#3657" class="InductiveConstructor Operator">_&amp;_</a> <a id="3661" class="Symbol">:</a> <a id="3663" href="#3617" class="Bound">A</a> <a id="3665" class="Symbol">→</a> <a id="3667" class="Symbol">∀</a> <a id="3669" class="Symbol">{</a><a id="3670" href="#3670" class="Bound">j</a> <a id="3672" class="Symbol">:</a> <a id="3674" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#211" class="Postulate Operator">Size&lt;</a> <a id="3680" href="#3630" class="Bound">i</a><a id="3681" class="Symbol">}</a> <a id="3683" class="Symbol">→</a> <a id="3685" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="3690" class="Symbol">(</a><a id="3691" href="#3611" class="Datatype">Tree</a> <a id="3696" href="#3617" class="Bound">A</a> <a id="3698" href="#3670" class="Bound">j</a><a id="3699" class="Symbol">)</a> <a id="3701" class="Symbol">→</a> <a id="3703" href="#3611" class="Datatype">Tree</a> <a id="3708" href="#3617" class="Bound">A</a> <a id="3710" href="#3630" class="Bound">i</a>

<a id="mapTree"></a><a id="3713" href="#3713" class="Function">mapTree</a> <a id="3721" class="Symbol">:</a> <a id="3723" class="Symbol">(</a><a id="3724" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="3726" class="Symbol">→</a> <a id="3728" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="3729" class="Symbol">)</a> <a id="3731" class="Symbol">→</a> <a id="3733" href="#3611" class="Datatype">Tree</a> <a id="3738" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="3740" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a> <a id="3742" class="Symbol">→</a> <a id="3744" href="#3611" class="Datatype">Tree</a> <a id="3749" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a> <a id="3751" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a>
<a id="3753" href="#3713" class="Function">mapTree</a> <a id="3761" href="#3761" class="Bound">f</a> <a id="3763" class="Symbol">(</a><a id="3764" href="#3764" class="Bound">x</a> <a id="3766" href="#3657" class="InductiveConstructor Operator">&amp;</a> <a id="3768" href="#3768" class="Bound">xs</a><a id="3770" class="Symbol">)</a> <a id="3772" class="Symbol">=</a> <a id="3774" href="#3761" class="Bound">f</a> <a id="3776" href="#3764" class="Bound">x</a> <a id="3778" href="#3657" class="InductiveConstructor Operator">&amp;</a> <a id="3780" href="../code/terminating-tricky-traversals/Post.Prelude.html#678" class="Function">map</a> <a id="3784" class="Symbol">(</a><a id="3785" href="#3713" class="Function">mapTree</a> <a id="3793" href="#3761" class="Bound">f</a><a id="3794" class="Symbol">)</a> <a id="3796" href="#3768" class="Bound">xs</a>
</pre>
So how do we use this stuff in our graph traversal?
Well first we'll need a coinductive Stream type:

<pre class="Agda"><a id="3914" class="Keyword">record</a> <a id="Stream"></a><a id="3921" href="#3921" class="Record">Stream</a> <a id="3928" class="Symbol">(</a><a id="3929" href="#3929" class="Bound">A</a> <a id="3931" class="Symbol">:</a> <a id="3933" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="3938" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="3939" class="Symbol">)</a> <a id="3941" class="Symbol">(</a><a id="3942" href="#3942" class="Bound">i</a> <a id="3944" class="Symbol">:</a> <a id="3946" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#179" class="Postulate">Size</a><a id="3950" class="Symbol">)</a> <a id="3952" class="Symbol">:</a> <a id="3954" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="3959" href="#3938" class="Bound">a</a> <a id="3961" class="Keyword">where</a>
  <a id="3969" class="Keyword">coinductive</a>
  <a id="3983" class="Keyword">field</a>
    <a id="Stream.head"></a><a id="3993" href="#3993" class="Field">head</a> <a id="3998" class="Symbol">:</a> <a id="4000" href="#3929" class="Bound">A</a>
    <a id="Stream.tail"></a><a id="4006" href="#4006" class="Field">tail</a> <a id="4011" class="Symbol">:</a> <a id="4013" class="Symbol">∀</a> <a id="4015" class="Symbol">{</a><a id="4016" href="#4016" class="Bound">j</a> <a id="4018" class="Symbol">:</a> <a id="4020" href="../code/terminating-tricky-traversals/Agda.Builtin.Size.html#211" class="Postulate Operator">Size&lt;</a> <a id="4026" href="#3942" class="Bound">i</a><a id="4027" class="Symbol">}</a> <a id="4029" class="Symbol">→</a> <a id="4031" href="#3921" class="Record">Stream</a> <a id="4038" href="#3929" class="Bound">A</a> <a id="4040" href="#4016" class="Bound">j</a>
<a id="4042" class="Keyword">open</a> <a id="4047" href="#3921" class="Module">Stream</a> <a id="4054" class="Keyword">public</a>

<a id="smap"></a><a id="4062" href="#4062" class="Function">smap</a> <a id="4067" class="Symbol">:</a> <a id="4069" class="Symbol">(</a><a id="4070" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="4072" class="Symbol">→</a> <a id="4074" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a><a id="4075" class="Symbol">)</a> <a id="4077" class="Symbol">→</a> <a id="4079" href="#3921" class="Record">Stream</a> <a id="4086" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="4088" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a> <a id="4090" class="Symbol">→</a> <a id="4092" href="#3921" class="Record">Stream</a> <a id="4099" href="../code/terminating-tricky-traversals/Post.Prelude.html#250" class="Generalizable">B</a> <a id="4101" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a>
<a id="4103" href="#4062" class="Function">smap</a> <a id="4108" href="#4108" class="Bound">f</a> <a id="4110" href="#4110" class="Bound">xs</a> <a id="4113" class="Symbol">.</a><a id="4114" href="#3993" class="Field">head</a> <a id="4119" class="Symbol">=</a> <a id="4121" href="#4108" class="Bound">f</a> <a id="4123" class="Symbol">(</a><a id="4124" href="#4110" class="Bound">xs</a> <a id="4127" class="Symbol">.</a><a id="4128" href="#3993" class="Field">head</a><a id="4132" class="Symbol">)</a>
<a id="4134" href="#4062" class="Function">smap</a> <a id="4139" href="#4139" class="Bound">f</a> <a id="4141" href="#4141" class="Bound">xs</a> <a id="4144" class="Symbol">.</a><a id="4145" href="#4006" class="Field">tail</a> <a id="4150" class="Symbol">=</a> <a id="4152" href="#4062" class="Function">smap</a> <a id="4157" href="#4139" class="Bound">f</a> <a id="4159" class="Symbol">(</a><a id="4160" href="#4141" class="Bound">xs</a> <a id="4163" class="Symbol">.</a><a id="4164" href="#4006" class="Field">tail</a><a id="4168" class="Symbol">)</a>
</pre>
And then we can use it to write our breadth-first traversal.

<pre class="Agda"><a id="bfs"></a><a id="4245" href="#4245" class="Function">bfs</a> <a id="4249" class="Symbol">:</a> <a id="4251" class="Symbol">⦃</a> <a id="4253" href="#4253" class="Bound">_</a> <a id="4255" class="Symbol">:</a> <a id="4257" href="../code/terminating-tricky-traversals/Post.Prelude.html#2916" class="Record">IsDiscrete</a> <a id="4268" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="4270" class="Symbol">⦄</a> <a id="4272" class="Symbol">→</a> <a id="4274" class="Symbol">(</a><a id="4275" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="4277" class="Symbol">→</a> <a id="4279" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="4284" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a><a id="4285" class="Symbol">)</a> <a id="4287" class="Symbol">→</a> <a id="4289" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="4291" class="Symbol">→</a> <a id="4293" href="#3921" class="Record">Stream</a> <a id="4300" class="Symbol">(</a><a id="4301" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="4306" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a><a id="4307" class="Symbol">)</a> <a id="4309" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a>
<a id="4311" href="#4245" class="Function">bfs</a> <a id="4315" href="#4315" class="Bound">g</a> <a id="4317" href="#4317" class="Bound">r</a> <a id="4319" class="Symbol">=</a> <a id="4321" href="#4062" class="Function">smap</a> <a id="4326" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#225" class="Field">fst</a> <a id="4330" class="Symbol">(</a><a id="4331" href="#2020" class="Function">fix</a> <a id="4335" class="Symbol">(</a><a id="4336" href="#3921" class="Record">Stream</a> <a id="4343" class="Symbol">_)</a> <a id="4346" class="Symbol">(</a><a id="4347" href="#4490" class="Function">f</a> <a id="4349" href="#4317" class="Bound">r</a> <a id="4351" href="../code/terminating-tricky-traversals/Post.Prelude.html#434" class="Function Operator">∘</a> <a id="4353" href="#4370" class="Function">push</a><a id="4357" class="Symbol">))</a>
  <a id="4362" class="Keyword">where</a>
  <a id="4370" href="#4370" class="Function">push</a> <a id="4375" class="Symbol">:</a> <a id="4377" href="#1897" class="Record">Thunk</a> <a id="4383" class="Symbol">(</a><a id="4384" href="#3921" class="Record">Stream</a> <a id="4391" class="Symbol">_)</a> <a id="4394" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a> <a id="4396" class="Symbol">→</a> <a id="4398" href="#3921" class="Record">Stream</a> <a id="4405" class="Symbol">_</a> <a id="4407" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a>
  <a id="4411" href="#4370" class="Function">push</a> <a id="4416" href="#4416" class="Bound">xs</a> <a id="4419" class="Symbol">.</a><a id="4420" href="#3993" class="Field">head</a> <a id="4425" class="Symbol">=</a> <a id="4427" class="Symbol">(</a><a id="4428" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a> <a id="4431" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="4433" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a><a id="4435" class="Symbol">)</a>
  <a id="4439" href="#4370" class="Function">push</a> <a id="4444" href="#4444" class="Bound">xs</a> <a id="4447" class="Symbol">.</a><a id="4448" href="#4006" class="Field">tail</a> <a id="4453" class="Symbol">=</a> <a id="4455" href="#4062" class="Function">smap</a> <a id="4460" class="Symbol">(</a><a id="4461" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">_,_</a> <a id="4465" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a> <a id="4468" href="../code/terminating-tricky-traversals/Post.Prelude.html#434" class="Function Operator">∘</a> <a id="4470" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#237" class="Field">snd</a><a id="4473" class="Symbol">)</a> <a id="4475" class="Symbol">(</a><a id="4476" href="#4444" class="Bound">xs</a> <a id="4479" class="Symbol">.</a><a id="4480" href="#1971" class="Field">force</a><a id="4485" class="Symbol">)</a>

  <a id="4490" href="#4490" class="Function">f</a> <a id="4492" class="Symbol">:</a> <a id="4494" class="Symbol">_</a> <a id="4496" class="Symbol">→</a> <a id="4498" href="#3921" class="Record">Stream</a> <a id="4505" class="Symbol">_</a> <a id="4507" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a> <a id="4509" class="Symbol">→</a> <a id="4511" href="#3921" class="Record">Stream</a> <a id="4518" class="Symbol">_</a> <a id="4520" href="../code/terminating-tricky-traversals/Post.Prelude.html#276" class="Generalizable">i</a>
  <a id="4524" href="#4490" class="Function">f</a> <a id="4526" href="#4526" class="Bound">x</a> <a id="4528" href="#4528" class="Bound">qs</a> <a id="4531" class="Keyword">with</a> <a id="4536" class="Symbol">(</a><a id="4537" href="#4526" class="Bound">x</a> <a id="4539" href="../code/terminating-tricky-traversals/Post.Prelude.html#3012" class="Function Operator">∈?</a> <a id="4542" href="#4528" class="Bound">qs</a> <a id="4545" class="Symbol">.</a><a id="4546" href="#3993" class="Field">head</a> <a id="4551" class="Symbol">.</a><a id="4552" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#237" class="Field">snd</a><a id="4555" class="Symbol">)</a> <a id="4557" class="Symbol">.</a><a id="4558" href="../code/terminating-tricky-traversals/Post.Prelude.html#1059" class="Field">does</a>
  <a id="4565" class="Symbol">...</a> <a id="4569" class="Symbol">|</a> <a id="4571" href="../code/terminating-tricky-traversals/Agda.Builtin.Bool.html#160" class="InductiveConstructor">true</a> <a id="4576" class="Symbol">=</a> <a id="4578" class="Bound">qs</a>
  <a id="4583" class="Symbol">...</a> <a id="4587" class="Symbol">|</a> <a id="4589" href="../code/terminating-tricky-traversals/Agda.Builtin.Bool.html#154" class="InductiveConstructor">false</a> <a id="4595" class="Symbol">=</a> <a id="4597" class="Symbol">λ</a> <a id="4599" class="Keyword">where</a> <a id="4605" class="Symbol">.</a><a id="4606" href="#3993" class="Field">head</a> <a id="4611" class="Symbol">→</a> <a id="4613" class="Symbol">(</a><a id="4614" class="Bound">x</a> <a id="4616" href="../code/terminating-tricky-traversals/Post.Prelude.html#556" class="InductiveConstructor Operator">∷</a> <a id="4618" class="Bound">qs</a> <a id="4621" class="Symbol">.</a><a id="4622" href="#3993" class="Field">head</a> <a id="4627" class="Symbol">.</a><a id="4628" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#225" class="Field">fst</a> <a id="4632" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#209" class="InductiveConstructor Operator">,</a> <a id="4634" class="Bound">x</a> <a id="4636" href="../code/terminating-tricky-traversals/Post.Prelude.html#556" class="InductiveConstructor Operator">∷</a> <a id="4638" class="Bound">qs</a> <a id="4641" class="Symbol">.</a><a id="4642" href="#3993" class="Field">head</a> <a id="4647" class="Symbol">.</a><a id="4648" href="../code/terminating-tricky-traversals/Agda.Builtin.Sigma.html#237" class="Field">snd</a><a id="4651" class="Symbol">)</a>
                        <a id="4677" class="Symbol">.</a><a id="4678" href="#4006" class="Field">tail</a> <a id="4683" class="Symbol">→</a> <a id="4685" href="../code/terminating-tricky-traversals/Post.Prelude.html#583" class="Function">foldr</a> <a id="4691" href="#4490" class="Function">f</a> <a id="4693" class="Symbol">(</a><a id="4694" class="Bound">qs</a> <a id="4697" class="Symbol">.</a><a id="4698" href="#4006" class="Field">tail</a><a id="4702" class="Symbol">)</a> <a id="4704" class="Symbol">(</a><a id="4705" href="#4315" class="Bound">g</a> <a id="4707" class="Bound">x</a><a id="4708" class="Symbol">)</a>
</pre>
How do we convert this to a list of lists?
Well, for this condition we would actually need to prove that there are only
finitely many elements in the graph.
We could actually use [Noetherian finiteness](https://arxiv.org/abs/1604.01186)
for this: though I have a working implementation, I'm still figuring out how to
clean this up, so I will leave it for another post.

# Traversing a Braun Tree


A recent paper [@NipkowS-CPP20] provided Coq proofs for some algorithms on Braun
trees [@okasakiThreeAlgorithmsBraun1997], which prompted me to take a look at
them again. 
This time, I came up with an interesting linear-time `toList` function, which
relies on the following peculiar type:

```haskell
newtype Q2 a
  = Q2
  { unQ2 :: (Q2 a -> Q2 a) -> (Q2 a -> Q2 a) -> a
  }
```

Even after coming up with the type myself, I still can't really make heads nor
tails of it.
If I squint, it starts to look like some bizarre church-encoded binary number
(but I have to *really* squint).
It certainly seems related to corecursive queues [@smith_lloyd_2009].

Anyway, we can use the type to write the following lovely `toList` function on a
Braun tree.

<span id="toListImpl">
```haskell
toList :: Tree a -> [a]
toList t = unQ2 (f t b) id id
  where
    f (Node x l r) xs = Q2 (\ls rs -> x : unQ2 xs (ls . f l) (rs . f r))
    f Leaf         xs = Q2 (\_  _  -> [])

    b = Q2 (\ls rs -> unQ2 (ls (rs b)) id id)
```
</span>

So can we convert it to Agda?

Not really!
As it turns out, this function is even more difficult to implement than one
might expect.
We can't even *write* the `Q2` type in Agda without getting in trouble.

<pre class="Agda"><a id="6242" class="Symbol">{-#</a> <a id="6246" class="Keyword">NO_POSITIVITY_CHECK</a> <a id="6266" class="Symbol">#-}</a>
<a id="6270" class="Keyword">record</a> <a id="Q2"></a><a id="6277" href="#6277" class="Record">Q2</a> <a id="6280" class="Symbol">(</a><a id="6281" href="#6281" class="Bound">A</a> <a id="6283" class="Symbol">:</a> <a id="6285" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="6290" href="../code/terminating-tricky-traversals/Post.Prelude.html#221" class="Generalizable">a</a><a id="6291" class="Symbol">)</a> <a id="6293" class="Symbol">:</a> <a id="6295" href="../code/terminating-tricky-traversals/Cubical.Core.Primitives.html#957" class="Function">Type</a> <a id="6300" href="#6290" class="Bound">a</a> <a id="6302" class="Keyword">where</a>
  <a id="6310" class="Keyword">inductive</a>
  <a id="6322" class="Keyword">field</a>
    <a id="Q2.q2"></a><a id="6332" href="#6332" class="Field">q2</a> <a id="6335" class="Symbol">:</a> <a id="6337" class="Symbol">(</a><a id="6338" href="#6277" class="Record">Q2</a> <a id="6341" href="#6281" class="Bound">A</a> <a id="6343" class="Symbol">→</a> <a id="6345" href="#6277" class="Record">Q2</a> <a id="6348" href="#6281" class="Bound">A</a><a id="6349" class="Symbol">)</a> <a id="6351" class="Symbol">→</a>
         <a id="6362" class="Symbol">(</a><a id="6363" href="#6277" class="Record">Q2</a> <a id="6366" href="#6281" class="Bound">A</a> <a id="6368" class="Symbol">→</a> <a id="6370" href="#6277" class="Record">Q2</a> <a id="6373" href="#6281" class="Bound">A</a><a id="6374" class="Symbol">)</a> <a id="6376" class="Symbol">→</a>
         <a id="6387" href="#6281" class="Bound">A</a>
<a id="6389" class="Keyword">open</a> <a id="6394" href="#6277" class="Module">Q2</a>
</pre>
`Q2` isn't strictly positive, unfortunately.

<pre class="Agda"><a id="6456" class="Symbol">{-#</a> <a id="6460" class="Keyword">TERMINATING</a> <a id="6472" class="Symbol">#-}</a>
<a id="toList"></a><a id="6476" href="#6476" class="Function">toList</a> <a id="6483" class="Symbol">:</a> <a id="6485" href="../code/terminating-tricky-traversals/Post.Prelude.html#4077" class="Datatype">Braun</a> <a id="6491" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="6493" class="Symbol">→</a> <a id="6495" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="6500" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a>
<a id="6502" href="#6476" class="Function">toList</a> <a id="6509" href="#6509" class="Bound">t</a> <a id="6511" class="Symbol">=</a> <a id="6513" href="#6587" class="Function">f</a> <a id="6515" href="#6509" class="Bound">t</a> <a id="6517" href="#6539" class="Function">n</a> <a id="6519" class="Symbol">.</a><a id="6520" href="#6332" class="Field">q2</a> <a id="6523" href="../code/terminating-tricky-traversals/Post.Prelude.html#3105" class="Function">id</a> <a id="6526" href="../code/terminating-tricky-traversals/Post.Prelude.html#3105" class="Function">id</a>
  <a id="6531" class="Keyword">where</a>
  <a id="6539" href="#6539" class="Function">n</a> <a id="6541" class="Symbol">:</a> <a id="6543" href="#6277" class="Record">Q2</a> <a id="6546" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a>
  <a id="6550" href="#6539" class="Function">n</a> <a id="6552" class="Symbol">.</a><a id="6553" href="#6332" class="Field">q2</a> <a id="6556" href="#6556" class="Bound">ls</a> <a id="6559" href="#6559" class="Bound">rs</a> <a id="6562" class="Symbol">=</a> <a id="6564" href="#6556" class="Bound">ls</a> <a id="6567" class="Symbol">(</a><a id="6568" href="#6559" class="Bound">rs</a> <a id="6571" href="#6539" class="Function">n</a><a id="6572" class="Symbol">)</a> <a id="6574" class="Symbol">.</a><a id="6575" href="#6332" class="Field">q2</a> <a id="6578" href="../code/terminating-tricky-traversals/Post.Prelude.html#3105" class="Function">id</a> <a id="6581" href="../code/terminating-tricky-traversals/Post.Prelude.html#3105" class="Function">id</a>

  <a id="6587" href="#6587" class="Function">f</a> <a id="6589" class="Symbol">:</a> <a id="6591" href="../code/terminating-tricky-traversals/Post.Prelude.html#4077" class="Datatype">Braun</a> <a id="6597" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a> <a id="6599" class="Symbol">→</a> <a id="6601" href="#6277" class="Record">Q2</a> <a id="6604" class="Symbol">(</a><a id="6605" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="6610" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a><a id="6611" class="Symbol">)</a> <a id="6613" class="Symbol">→</a> <a id="6615" href="#6277" class="Record">Q2</a> <a id="6618" class="Symbol">(</a><a id="6619" href="../code/terminating-tricky-traversals/Post.Prelude.html#507" class="Datatype">List</a> <a id="6624" href="../code/terminating-tricky-traversals/Post.Prelude.html#237" class="Generalizable">A</a><a id="6625" class="Symbol">)</a>
  <a id="6629" href="#6587" class="Function">f</a> <a id="6631" href="../code/terminating-tricky-traversals/Post.Prelude.html#4113" class="InductiveConstructor">leaf</a>         <a id="6644" href="#6644" class="Bound">xs</a> <a id="6647" class="Symbol">.</a><a id="6648" href="#6332" class="Field">q2</a> <a id="6651" href="#6651" class="Bound">ls</a> <a id="6654" href="#6654" class="Bound">rs</a> <a id="6657" class="Symbol">=</a> <a id="6659" href="../code/terminating-tricky-traversals/Post.Prelude.html#542" class="InductiveConstructor">[]</a>
  <a id="6664" href="#6587" class="Function">f</a> <a id="6666" class="Symbol">(</a><a id="6667" href="../code/terminating-tricky-traversals/Post.Prelude.html#4130" class="InductiveConstructor">node</a> <a id="6672" href="#6672" class="Bound">x</a> <a id="6674" href="#6674" class="Bound">l</a> <a id="6676" href="#6676" class="Bound">r</a><a id="6677" class="Symbol">)</a> <a id="6679" href="#6679" class="Bound">xs</a> <a id="6682" class="Symbol">.</a><a id="6683" href="#6332" class="Field">q2</a> <a id="6686" href="#6686" class="Bound">ls</a> <a id="6689" href="#6689" class="Bound">rs</a> <a id="6692" class="Symbol">=</a> <a id="6694" href="#6672" class="Bound">x</a> <a id="6696" href="../code/terminating-tricky-traversals/Post.Prelude.html#556" class="InductiveConstructor Operator">∷</a> <a id="6698" href="#6679" class="Bound">xs</a> <a id="6701" class="Symbol">.</a><a id="6702" href="#6332" class="Field">q2</a> <a id="6705" class="Symbol">(</a><a id="6706" href="#6686" class="Bound">ls</a> <a id="6709" href="../code/terminating-tricky-traversals/Post.Prelude.html#434" class="Function Operator">∘</a> <a id="6711" href="#6587" class="Function">f</a> <a id="6713" href="#6674" class="Bound">l</a><a id="6714" class="Symbol">)</a> <a id="6716" class="Symbol">(</a><a id="6717" href="#6689" class="Bound">rs</a> <a id="6720" href="../code/terminating-tricky-traversals/Post.Prelude.html#434" class="Function Operator">∘</a> <a id="6722" href="#6587" class="Function">f</a> <a id="6724" href="#6676" class="Bound">r</a><a id="6725" class="Symbol">)</a>
</pre>

Apparently this problem of strict positivity for breadth-first traversals has
come up before: @bergerMartinHofmannCase2019; @hofmannNonStrictlyPositive1993.

# Wait---Where did Q2 Come From?

Update 31/01/2020

Daniel Peebles ([\@copumpkin](https://twitter.com/copumpkin) on twitter) replied
to my tweet about this post with the following:

> Interesting! Curious *how* you came up with that weird type at the end. It
> doesn’t exactly feel like the first thing one might reach for and it would be
> interesting to see some writing on the thought process that led to it
>
> [Dan P (\@copumpkin), Jan 30, 2020.](https://twitter.com/copumpkin/status/1222681927854936065)

So that's what I'm going to add here!

Let's take the Braun tree of the numbers 1 to 15:

```
     ┌8
   ┌4┤
   │ └12
 ┌2┤
 │ │ ┌10
 │ └6┤
 │   └14
1┤
 │   ┌9
 │ ┌5┤
 │ │ └13
 └3┤
   │ ┌11
   └7┤
     └15
```

Doing a normal breadth-first traversal for the first two levels is fine (1, 2,
3): it starts to fall apart at the third level (4, 6, 5, 7).
Here's the way we should traverse it: "all of the left branches, and then all of
the right branches".
So, we will have a queue of trees.
We take the root element of each tree in the queue, and emit it, and then we
add all of the *left* children of the trees in the queue to one queue, and then
all the *right* children to another, and then concatenate them into a new queue
and we start again.
We can stop whenever we hit an empty tree because of the structure of the Braun
tree.
Here's an ascii diagram to show what's going on:

```
     ┌8   |     ┌8    |     ┌8     |       8
   ┌4┤    |   ┌4┤     |    4┤      |
   │ └12  |   │ └12   |     └12    |       9
 ┌2┤      |  2┤       |            |
 │ │ ┌10  |   │ ┌10   |     ┌9     |       10
 │ └6┤    |   └6┤     |    5┤      |
 │   └14  |     └14   |     └13    |       11
1┤       -->        ----->      -------->
 │   ┌9   |     ┌9    |     ┌10    |       12
 │ ┌5┤    |   ┌5┤     |    6┤      |
 │ │ └13  |   │ └13   |     └14    |       13
 └3┤      |  3┤       |            |
   │ ┌11  |   │ ┌11   |     ┌11    |       14
   └7┤    |   └7┤     |    7┤      |
     └15  |     └15   |     └15    |       15

         1,         2, 3,       4, 5, 6, 7,   8, 9, 10, 11, 12, 13, 14, 15
```

If we want to do this in Haskell, we have a number of options for how we would
represent queues: as ever, though, I much prefer to use vanilla lists and time
the reversals so that they stay linear.
Here's what that looks like:

```haskell
toList :: Tree a -> [a]
toList t = f t b [] []
  where
    f (Node x l r) xs ls rs = x : xs (l : ls) (r : rs)
    f Leaf         _ _  _  = []

    b ls rs = foldr f b (reverse ls ++ reverse rs) [] []
```

Any place we see a `foldr` being run after a reverse or a concatenation, we know
that we can remove a pass (in actual fact rewrite rules will likely do this
automatically for us).

```haskell
toList :: Tree a -> [a]
toList t = f b t [] []
  where
    f (Node x l r) xs ls rs = x : xs (l : ls) (r : rs)
    f Leaf         _  _  _  = []

    b ls rs = foldl (flip f) (foldl (flip f) b rs) ls [] []
```

Finally, since we're building up the lists with `:` (in a linear way, i.e. we
will not use the intermediate queues more than once), and we're immediately
consuming them with a fold, we can deforest the intermediate list, replacing
every `:` with `f` (actually, it's a little more tricky than that, since we
replace the `:` with the *reversed* version of `f`, i.e. the one you would pass
to `foldr` if you wanted it to act like `foldl`. This trick is explained in more
detail in [this post](2019-05-08-list-manipulation-tricks.html)).

```haskell
toList :: Tree a -> [a]
toList t = f t b id id
  where
    f (Node x l r) xs ls rs = x : xs (ls . f l) (rs . f r)
    f Leaf         _ _ _ = []

    b ls rs = ls (rs b) id id
```

Once you do that, however, you run into the "cannot construct the infinite type"
error.
To be precise:

> ```
> • Occurs check: cannot construct the infinite type:
>     a3 ~ (a3 -> c0) -> (a3 -> c1) -> [a2]
> ```

And this gives us the template for our newtype!
It requires some trial and error, but you can see where some of the recursive
calls are, and what you eventually get is the following:

```haskell
newtype Q2 a
  = Q2
  { unQ2 :: (Q2 a -> Q2 a) -> (Q2 a -> Q2 a) -> [a]
  }
```

(You can remove the list type constructor at the end, I did as I thought it made
it slightly more general).
And from there we get back to [the `toList` function](#toListImpl).



# References
