---
title: How to use GitHub actions for LaTeX, literate Haskell, and Agda
tags: Haskell, Agda, LaTeX
---

I'm currently working on my master's thesis, and because it contains a lot of
Agda and a complex compiling system, I set up GitHub actions to compile the
thesis automatically on every commit.
On every push, the script runs on GitHub's servers, type checking all the Agda
code and compiling the paper, and then it deploys it to a web page which I can
point my supervisor at.
It takes about 3 minutes from the commit to deploy the fully rendered paper.

It's great for letting people look at the paper and collaborate a little without
having a full Agda or Haskell install.
It ended up being extremely complex to set up, and I sunk way too much time into
it, so I thought I'd share the finished thing here to save others some of the
work of doing it.
Basically, if you're thinking of writing a paper in the future which uses
literate Haskell or Agda, and you'd like it to compile remotely in under four
hours, this might be the tutorial for you.

# The LaTeX Setup

First, I'll go through a little how I structure the paper and all the files
locally.
I usually have a main file, called something like `paper.tex`, which imports
each section of the paper I'm interested in from a folder called `sections/` or
something.
I use latexmk and spacemacs: this lets me edit each .tex file individually, and
when I hit `SPC-m-a` in a file the whole paper is compiled and my pdf viewer
jumps to the point my cursor was at in spacemacs.
I've written a little about [this editing system
before](2019-03-14-more-agda-tips.html), so I won't go into it in a huge amount
of detail here, but there's one small extra thing that I've added to my setup:
if you structure the paper with a `sections/` subfolder with separate files for
all sections (as I do), you can add the following to the end of each `.tex` file
so that `SPC-m-a` works even from the tex files being imported:

```
%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../paper"
%%% End:%
```

In the `.latexmkrc` file also you should have the following:

```
@default_files = ('paper.tex');
```

This just means that you'll never accidentally compile a file on its own when
you meant it to be part of `paper.tex`.

The next part is how to organise code.
My preferred method is to have a subfolder (called `agda/`), which contains all
your code as an actual agda *library*.
I then structure my code much as I would if I was just writing a library, and
then I put tags around any lines I want to have in the paper.
I have the following file in my thesis, for instance:

```tex
\begin{code}
{-# OPTIONS --cubical --safe #-}

module Function.Injective.Base where

open import Level
open import Path
open import Data.Sigma

Injective : (A → B) → Type _
\end{code}
%<*injective>
\begin{code}
Injective f = ∀ x y → f x ≡ f y → x ≡ y
\end{code}
%</injective>
```

As an agda file, it defines injective functions in the usual way.
But I also want to have a definition of injective functions in the paper: what I
can do is stick the line

```tex
\ExecuteMetaData[agda/Function/Injective/Base.tex]{injective}
```

in the paper and then the following Agda code will be rendered:

```agda
Injective f = ∀ x y → f x ≡ f y → x ≡ y
```

I find that often when writing literate code ordering and structure becomes a
huge issue: you end up having to choose a structure that makes for good prose
but terribly-structured code, or vice versa.
This way separates the library from the paper somewhat, so you can structure
each in the way that is best for it.

Also, it means you can compile the whole Agda library to html, producing a site
alongside the paper.
This is handy as a way to produce an artefact in tandem with the paper, or just
as a way to provide a nice clickable way to navigate and read the code without
having to download Agda and typecheck it.

All of this equally applies to Haskell code, by the way: I usually make a cabal
project in a folder called `haskell/`, and then I grab lines of code as I need
them into the paper.

# GitHub Actions

So that's how I do things locally, with latexmk and spacemacs.
It's a reasonably quick system (for LaTeX), from the time I press `SPC-m-a` to
the pdf being refreshed is about 10 seconds on average.

It is extremely tied to my particular setup, though: if someone else tries to
compile the paper with a different version of ghc or LaTeX or Agda, or even a
different version of the Agda standard library installed on their machine, it
probably won't work!
There are hundreds of tiny little bits of configuration on my machine that I'm
not aware of or have forgotten, so trying to replicate it on someone else's
computer is near impossible.
It's a perfect candidate for a remote builder, in other words.

This is where [GitHub actions](https://github.com/features/actions) come in:
it's a new CI service GitHub offers, which I decided to try use to compile my
paper.
I went with GitHub actions over something like travis because I've had a better
experience with GitHub's ease of use and interfaces in the past, and also
because I wanted to integrate with GitHub pages to serve the paper from a web
page.
Also I already pay for pro membership on github, so I figured I might get a good
bit of server time. (it turns out the pro membership doesn't offer much more
than free does in this regard)

# Installing GHC, Cabal, and all the Haskell Stuff

We'll need GHC to typecheck our literate Haskell files, but also Agda itself is
written in Haskell, as is lhs2TeX, and several other tools, so it will be useful
to have a Haskell install on the remote machine as a first step.
Thankfully, the hard part here has already been worked out for us: the
[setup-haskell](https://github.com/actions/setup-haskell) action can install
cabal and a ghc version for us without much fuss (it also works excellently with
stack; that's how I compile this website with github actions).
Here's the particular step in the workflow which uses this action:

```yaml
- name: Install ghc and cabal
  uses: actions/setup-haskell@v1.1
  with:
    ghc-version: ${{ matrix.ghc-ver }}
    cabal-version: ${{ matrix.cabal-ver }}
```

One thing that's important to include is the following:

```yaml
- name: Put cabal programs in PATH
  run: echo "::add-path::~/.cabal/bin"
```

For executables installed with cabal to be available in general you have to add
`~/.cabal/bin` to your path, but unfortunately the GitHub actions syntax for
doing that is the weird thing you see above.
I would really love if GitHub actions made this oddity much more visible somehow
(realising that `export PATH=...` didn't work cost me a couple hours at least).

# Caching

Since we're going to set up a full GHC, Haskell, Agda, and LaTeX install, the
whole install process will likely take several hours (3-4 by my estimate).
That's absolutely too long for this system to be useful for checking pull
requests and the like (and it also can run you into cost troubles with server
time etc.)
As a fix I use caching in my setup: there are probably better ways to achieve
the same result, but it has got the total time for the action to run down to
about 3 minutes, so I'm sticking with it for now.

There are two important things that the caching steps do.
First, if a particular bit of source code or dependency doesn't change, the
cache should copy over the old compile as best it can.
Secondly, if there is a minor change, the cache should copy over the most recent
closest compile to allow for incremental compiles: this second step is
absolutely essential for quick Agda compiles.
Here's the yaml code:

```yaml
    - uses: actions/cache@v2
      name: Cache cabal packages
      id: cache-cabal
      with:
        path: |
          ~/.cabal/packages
          ~/.cabal/store
          ~/.cabal/bin
          dist-newstyle
        key: ${{ runner.os }}-${{ matrix.ghc-ver }}-${{ matrix.cabal-ver }}-${{ matrix.agda-ref }}-${{ hashFiles('main/haskell/haskell.cabal') }}
        restore-keys: ${{ runner.os }}-${{ matrix.ghc-ver }}-${{ matrix.cabal-ver }}-${{ matrix.agda-ref }}
```

The key uses matrix variables set for the versions of each program we include;
the `restore-keys` field is searched for (by prefix) if an exact match for the
key isn't found.

# Installing Agda

For the paper I was working on I needed to use the development version of Agda,
which unfortunately meant I couldn't run `apt-get install agda` or whatever.
This *also* meant that I ran into some bugs in GHC when trying to compile Agda
from source: basically, it is not possible to compile Agda with `-O2`: it will
heap overflow. 
If you set the allowed amount of memory to something higher it will still not
work, it will just take longer.

The highest level of optimisation I could enable was `-O2`, and even then I
found it was useful to increase GHC's permitted amount of memory just to be
safe.
Here's the code:

```yaml
- name: Install Agda
  if: steps.cache-cabal.outputs.cache-hit != 'true'
  run: |
    cabal update
    cabal install --overwrite-policy=always --ghc-options='-O2 +RTS -M6G -RTS' alex-3.2.5
    cabal install --overwrite-policy=always --ghc-options='-O2 +RTS -M6G -RTS' happy-1.19.12
    cd agda
    mkdir -p doc
    touch doc/user-manual.pdf
    cabal install --overwrite-policy=always --ghc-options='-O1 +RTS -M6G -RTS'
```

# Installing Agda Libraries

Agda doesn't have a sophisticated dependency management system, unfortunately,
so you have to do quite a few things by hand if you want to get a version of
(say) the standard library on the remote machine.
The main thing is that you will want to typecheck everything in the library and
cache the build files: this will save a tonne of time.
Typechecking each file is a little tricky, though: the fastest way (in my
experience) is to make a file called something like `Everything.agda` and put an
import statement for every agda file in the project in it, and then typecheck
that.
This is quicker than typechecking every file individually.
Here's a bash script which generates an "Everything" file:

```bash
#!/usr/bin/env bash

cd agda || exit
if [ -f "$1.agda" ]; then
    echo "file agda/$1.agda already exists: you must supply a module name which does not already exist"
    exit 17
fi
everything_file=$(mktemp)
trap "rm -f $everything_file" 0 2 3 15
echo "module $1 where" > $everything_file
find . -type f \( -name "*.agda" -o -name "*.lagda" \) \
        | cut -c 3- \
        | cut -f1 -d'.' \
        | sed 's/\//\./g' \
        | sed 's/^/open import /' \
              >> $everything_file
mv $everything_file $1.agda
```

Unfortunately Agda's standard library actually contains files which do *not*
typecheck (in the deprecated files): you need to include logic to avoid these
files to have everything work properly.

# A little bit of venting about GitHub Actions

All in all, my feelings on the GitHub actions system are mixed.
The setup I have does work now, and it works quite well, compiling everything
quick enough that it's possible for someone to edit the tex files online without
having anything but a web browser.
However it was not easy to get to that point: previous iterations of the build
script took multiple hours to render the paper, which meant that debugging the
script itself was absolute hell.
I'd make a small change, hit commit, and an hour later I'd get an email saying I
forgot a colon (or something).

Part of the problem was that the language for writing an actual action is quite
unclear: it's kind of bash, but not really.
It's in a yaml file (the structure of which was also quite unclear to me), and
there are all kinds of gotchas that are extremely frustrating.
For instance, I needed to install Agda using cabal on the remote machine.
That's not *too* difficult (although, I should stress, it's not easy either):
there's a package already out there which installs ghc and cabal, and from there
I can run `cabal install Agda` or whatever and it works.
Except, as Haskellers might know, you need to have `~/.cabal/bin` in your PATH
to then have access to agda.
Here's the problem: the usual `PATH=$PATH:~/.cabal/bin` won't work!
You need to use the GitHub actions special syntax: `echo "::add-path::~/.cabal/bin"`.
Figuring this out took me several hours, especially seeing as I had to reinstall
cabal and ghc remotely every time I wanted to try a new version.
Also, that path isn't available in scripts that the action runs (as in `sh
my-script.sh`) as far as I can tell, so there's another annoyance.

Figuring this stuff out would be helped hugely if I could run the action
locally: remotely it's being run from inside a docker container, after all, so I
assumed that I should be able to put that container on my machine and debug
locally without the round-trip to GitHub's servers.
And there is indeed a [repo](https://github.com/nektos/act) which claims to let
you do this.
Unfortunately, running the action locally is subtly different from running it
remotely, to the extent that it kind of defeats the purpose.
Several actions straight-up won't work when you try run them locally: if you try
to download a repo form GitHub, for instance, the local runner won't have the
permissions that the remote one does, so it will fail.
While attempting to get the local action to work I began to realise that I had
would need two separate scripts: one for the local action, and another for the
remote.
Since the whole purpose had been to debug the remote script quickly, I decided
to drop the local stuff and just do everything remotely.

# Back to the setup!
