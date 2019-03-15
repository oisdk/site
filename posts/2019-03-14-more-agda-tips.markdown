---
title: More Agda Tips
tags: Agda
series: Agda Tips
---

# Literate Agda

For including Agda code in LaTeX files, Agda's built-in literate programming
support is a great tool. It typesets code well, and ensures that it typechecks
which can help avoid typos.

### Embedding Agda Code in LaTeX

I write the LaTeX document in one file, and the Agda code in another `.lagda`
file. Using the
[catchfilebetweentags](https://ctan.org/pkg/catchfilebetweentags?lang=en) LaTeX
package, I can then embed snippets of the Agda code into the LaTeX document. For
instance, in a file named `Lists.lagda` I can have the following:

```agda
%<*head-type>
\begin{code}
head : List A → Maybe A
\end{code}
%</head-type>

\begin{code}
head [] = nothing
head (x ∷ xs) = just x
\end{code}
```

Then, after compiling the Agda file with `agda --latex --output-dir=.
Lists.lagda`, I can embed the snippet `head : List A → Maybe A` into the TeX
file like so:

```latex
\ExecuteMetaData[Lists.tex]{head-type}
```

### Dealing with Unicode

Most Agda source code will be Unicode-heavy, which doesn't work well in LaTeX.
There are a few different ways to deal with this: you could use XeTeX, which
handles Unicode better, for instance. I found it easier to use the
[ucs](https://ctan.org/pkg/ucs?lang=en) package, and write a declaration for
each Unicode character as I came across it. For the `∷` character above, for
instance, you can write:

```latex
\usepackage{ucs}
\DeclareUnicodeCharacter{8759}{\ensuremath{\squaredots}}
```

### Live Reloading

For plain LaTeX code, I use [Spacemacs](http://spacemacs.org/) and
[Skim](https://skim-app.sourceforge.io/) to get live reloading. When I save the
LaTeX source code, the Skim window refreshes and jumps to the point my editing
cursor is at. I use elisp code from
[this](https://mssun.me/blog/spacemacs-and-latex.html) blog post.

For Agda code, live reloading gets a little trickier. If I edit an Agda source
file, the LaTeX won't automatically recompile it. However, based on
[this](https://tex.stackexchange.com/questions/142540/configuring-latexmk-to-use-a-preprocessor-lhs2tex)
stack exchange answer, you can put the following `.latexmkrc` file in the same
directory as your `.lagda` files and your `.tex` file:

```
add_cus_dep('lagda','tex',1,'lagda2tex');

sub lagda2tex {
    my $base = shift @_;
    return system('agda', '--latex', '--latex-dir=.', "$base.lagda");
}
```

This will recompile the literate Agda files whenever they're changed. Just make
sure to run `agda --latex --output-dir=.` once for every literate Agda file when
you initially set up the document. After that, latexmk will take over and do it
automatically, but the `.tex` files need to be present initially for it to
recognise the dependency.

# Flags for Debugging

There are a number of undocumented flags you can pass to Agda which are
absolutely invaluable when it comes to debugging. One of them [can tell you more
about termination
checking](http://oleg.fi/gists/posts/2018-08-29-agda-termination-checker.html),
another reports on type checking (`tc`), another for profiling (`profile`), and so on. Set the verbosity level
(`agda -v 100`) to get more or less info.

# Type Checking Order

Agda does type checking from left to right. This isn't always desired: as an
example, if we want to annotate a value with its type, we can use the following
function:

```agda
the : ∀ {a} (A : Set a) → A → A
the _ x = x

example : _
example = the ℕ 3
```

Coming from Haskell, though, this is the wrong way around. We usually prefer to
write something like `3 :: Int`. We can't write that as a simple function in
Agda, though, so we instead
use a syntax declaration:

```agda
syntax the ty x = x ∷ ty

example : _
example = 3 ∷ ℕ
```

Changing the order of type checking can also [speed up typechecking in some
cases](https://github.com/agda/agda-stdlib/issues/622#issue-411010875). There's
more information about syntax declarations in [Agda's
documentation](https://agda.readthedocs.io/en/latest/language/syntax-declarations.html).
