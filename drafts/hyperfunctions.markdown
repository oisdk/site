---
title: Hyperfunctions
tags: Haskell
bibliography: Hyperfunctions.bib
---

Check out this bizarre type:

```haskell
newtype a -&> b = Hyp { invoke :: (b -&> a) -> b } 
```

This is a *hyperfunction* [@launchbury_zip_2000; @krstic_category_2000;
@launchbury_coroutining_2013], and as well as being extremely weird, it has a
bunch of mind-bending properties, and a surprising number of practical uses.
