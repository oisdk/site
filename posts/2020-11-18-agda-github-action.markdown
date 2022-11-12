---
title: How to set up GitHub Actions for your Agda project
tags: Agda
---

## Update 2022-11-12

The best approach to this now is probably to use this action, specifically set up
for Agda:

* https://github.com/wenkokke/setup-agda

I'll leave the rest of this post here, but bear in mind the advice is outdated.

---

Recently travis-ci.org announced that they were closing down, and moving to
travis-ci.com.
For people who use the service, this basically means that the free component is
going away, and you'll have to pay in the future.

As a result, a lot of people are looking to move to another ci service, so I
thought I'd put this short guide together on how to use GitHub actions to
typecheck an Agda project and host the rendered code through GitHub pages.
The system I have is quite fast: for a quite large project it takes about a
minute from pushing for the action to complete.

If you just want to use the same script as me, you can see it
[here](https://github.com/oisdk/agda-playground/blob/master/.github/workflows/compile.yaml):
the rest of this post will just be going through that script and explaining it.

# Setting up a Basic Action

First things first: in order to make an action, you need to put a YAML file in
the `.github/workflows` directory of your repository.
You can have the following lines at the start:

```yaml
name: Compile Agda and Deploy HTML
on:
  push:
    branches:
      - master
```

This gives a name for the action (which will show up in the actions tab online
for the repo), and says that the action should be run whenever there's a push to
the branch named `master`.

We then list the "jobs" the actions does: just one for this action, called `build`:

```yaml
jobs:
  build:
```

# Configuring The Runner

GitHub actions run on GitHub's servers, the specifications of which can be seen
[here](https://docs.github.com/en/free-pro-team@latest/actions/reference/specifications-for-github-hosted-runners).
For this action we won't need anything special, so we'll just use the following:

```yaml
    runs-on: ubuntu-18.04
```

Next we will have the matrix:


```yaml
    strategy:
      matrix:
        cubical-ref: ["v0.2"]
        agda-ref: ["v2.6.1.1"]
        ghc-ver: ["8.10.2"]
        cabal-ver: ["3.4.0.0"]
```

I'm using this matrix as a crude system for environment variables; if this was a
CI for some software I wanted to deploy, you could include multiple values for
each variable here, to check that the whole thing runs properly with each.

# Caching

We're now onto the "steps" portion of the script, where we write small
bash-esque script to be run.
As such we have the line:


```yaml
    steps:
```

The first step is to cache all the cabal packages we're going to install.
Agda takes about 45 minutes to install so this step is crucial:

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
        key: ${{ runner.os }}-${{ matrix.ghc-ver }}-${{ matrix.cabal-ver }}-${{ matrix.agda-ref }}
```

The `path` field tells the action which folders to cache, the `key` field tells
it what key to store them under.

# Installing Agda

To install Agda we first need to install cabal:

```yaml
    - name: Install cabal
      if: steps.cache-cabal.outputs.cache-hit != 'true'
      uses: actions/setup-haskell@v1.1.3
      with:
        ghc-version: ${{ matrix.ghc-ver }}
        cabal-version: ${{ matrix.cabal-ver }}
```

The `if` field here allows us to skip this step if we had a cache hit previously
(i.e. if Agda is already installed).

Next we need to ensure that all of the programs installed by cabal are in the path:

```yaml
    - name: Put cabal programs in PATH
      run: echo "~/.cabal/bin" >> $GITHUB_PATH
```

And then we download and install Agda (along with some dependencies that aren't
installed automatically):

```yaml
    - name: Download Agda from github
      if: steps.cache-cabal.outputs.cache-hit != 'true'
      uses: actions/checkout@v2
      with:
        repository: agda/agda
        path: agda
        ref: ${{ matrix.agda-ref }}
      
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

The strange flags to `cabal install` here are *probably* necessary: I was
running out of memory when I tried to install Agda without them.
This might be fixed in future versions of Agda.

# Installing Agda Dependencies

We next need to install any Agda libraries your code depends on.
For instance, in my project, I use the cubical library: since Agda doesn't have
a package manager, we basically have to handle all the versioning and so on
manually.
Also, in order to speed up the build we have to cache the typecheck files for
the library.

```yaml
    - name: Checkout cubical library
      uses: actions/checkout@v2
      with:
        repository: agda/cubical
        path: cubical
        ref: ${{ matrix.cubical-ref }}

    - name: Cache cubical library
      uses: actions/cache@v2
      id: cache-cubical
      with:
        path: ~/cubical-build
        key: ${{ runner.os }}-${{ matrix.agda-ver }}-${{ matrix.cubical-ref }}
```

So the library is accessible as an import we need to put it in the Agda library list:

```yaml
    - name: Put cubical library in Agda library list
      run: |
        mkdir -p ~/.agda/
        touch ~/.agda/libraries
        echo "$GITHUB_WORKSPACE/cubical/cubical.agda-lib" > ~/.agda/libraries
```

We then need to typecheck the library: this bit is a little tricky, since not
all files in the cubical library actually typecheck.

```yaml
    - name: Compile cubical library
      if: steps.cache-cubical.outputs.cache-hit != 'true'
      run: |
        cd $GITHUB_WORKSPACE/cubical
        agda Cubical/Core/Everything.agda
        agda Cubical/Foundations/Everything.agda
        find Cubical/Data -type f -name "*.agda" | while read -r code ; do
            agda $code
        done
        find Cubical/HITs -type f -name "*.agda" | while read -r code ; do
            agda $code
        done
        cp -f -r _build/ ~/cubical-build
```

Finally, if the cubical library was already typechecked then we don't need to do
any of that, and we instead just retrieve it from the cache:

```yaml
    - name: Retrieve cubical library
      if: steps.cache-cubical.outputs.cache-hit == 'true'
      run: |
        mkdir -p cubical/_build
        cp -f -r ~/cubical-build/* cubical/_build
```

# Typechecking the library

Finally we have to typecheck the library itself.
We want to cache the output from this step as well, but importantly we want to
support incremental recompilation: i.e. if we only make a small change in one
file we don't want to have to typecheck every other.
We can do this with `restore-keys` in the cache:

```yaml
    - name: Checkout main
      uses: actions/checkout@v2
      with:
        path: main

    - uses: actions/cache@v2
      name: Cache main library
      id: cache-main
      with:
        path: ~/main-build
        key: html-and-tex-${{ runner.os }}-${{ matrix.agda-ver }}-${{ matrix.cubical-ref }}-${{ hashFiles('main/**') }}
        restore-keys: |
          html-and-tex-${{ runner.os }}-${{ matrix.agda-ver }}-${{ matrix.cubical-ref }}-
          html-and-tex-${{ runner.os }}-${{ matrix.agda-ver }}-

    - name: Retrieve main library
      if: steps.cache-main.outputs.cache-hit == 'true'
      run: cp -f -R ~/main-build/* $GITHUB_WORKSPACE/main
```

Finally, we need to make an "Everything" file: this is an Agda module which
contains an import for every module in the project.
Typechecking this file is faster than typechecking each file individually.

```yaml
    - name: Compile main library
      if: steps.cache-main.outputs.cache-hit != 'true'
      run: |
        mkdir -p ~/main-build/_build
        cp -f -R ~/main-build/_build $GITHUB_WORKSPACE/main/_build
        rm -r ~/main-build
        cd main
        find . -type f \( -name "*.agda" -o -name "*.lagda" \) > FileList
        sort -o FileList FileList
        echo "{-# OPTIONS --cubical #-}" > Everything.agda
        echo "" >> Everything.agda
        echo "module Everything where" >> Everything.agda
        echo "" >> Everything.agda
        echo "-- This file imports every module in the project. Click on" >> Everything.agda
        echo "-- a module name to go to its source." >> Everything.agda
        echo "" >> Everything.agda
        cat FileList | cut -c 3-               \
                     | cut -f1 -d'.'           \
                     | sed 's/\//\./g'         \
                     | sed 's/^/open import /' \
                     >> Everything.agda
        rm FileList
        agda --html --html-dir=docs Everything.agda
        rm Everything.agda
        cd ..
        cp -f -R main/ ~/main-build/
```

And then we need to deploy the generated `html` so we can see the rendered
library.

```yaml
    - name: Deploy html to github pages
      uses: peaceiris/actions-gh-pages@v3
      with:
        github_token: ${{ secrets.GITHUB_TOKEN }}
        publish_dir: main/docs
```

This last step will need you to turn on the github pages setting in your
repository, and have it serve from the `gh-pages` branch.

# Conclusion

Hopefully this script will be useful to some other people!
The first time it runs it should take between 30 minutes and an hour;
subsequently it takes about a minute for me.
