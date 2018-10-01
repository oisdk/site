---
title: Literate Programming in Haskell and Agda
tags: Haskell, Agda, LaTeX
---

As I mentioned in the last post, I'm currently in the middle of quite a long
Agda project, much of which is geared towards a LaTeX output, and along the way
I've developed a process which has worked surprisingly well (for me). First,
I'll detail my LaTeX editing setup, then I'll show the three main ways of
getting code into a LaTeX document. While I only mention Haskell and Agda in the
title here, parts of the process can be applied to any language (or, indeed, any
LaTeX editing process).

# The PDF Viewer

This might seem like a strange place to start, but it's important for the
editing process, especially as LaTeX isn't a
[WYSIWG](https://en.wikipedia.org/wiki/WYSIWYG) process. On macOS, you have two
built-in viewers: Preview and Safari. What we want is *live updating* of the
document, as you edit it. For this blog, for instance, I use
[LiveReload](http://livereload.com/) in combination with Hakyll's `watch`
command. This means I can edit the markdown for the site in emacs, and whenever
I hit save it will recompile and refresh the page in Safari (Firefox now,
actually, since Safari 12's browser extensions are severely hamstrung).

Getting the same thing for PDFs is tough. When I couldn't find a ready-made
solution, I whipped out the Apple Script, and tried to hack it together myself.
The problem is a little harder than it may seem, because so many minor niggles
actually turn out to defeat the purpose of the whole enterprise. The basic idea
was to watch the `.tex` file and reload the Preview window on a change. Getting
*that* up and running was practically easy: the reloading, on the other hand,
was a nightmare. First it would scroll to the top of the document, rather than
staying in the position I reloaded it at. This means I'd have to manually scroll
back to where I was on every change. Awful.

Presuming you figure out how to fix that (I didn't), you now realize that the
window is brought to the front every time it's reloaded, meaning you'll have to
alt-tab on every save. Ugh. You find an obscure way to reload a document without
bringing the window to the front: turns out this sometimes *doesn't* reload the
document. Instead, you note the window permutation before you reload, and
reshuffle them after the reloading operation. This takes about 3-4 seconds to do
on every reload, and works about 60% of the time. 

My eye is twitching a little just remembering it, so I'll cut to the chase: just
use [Skim](https://skim-app.sourceforge.io/). It's a little uglier and less
"native-feeling" than Preview, and it's hosted on sourceforge which was [a
little
worrying](https://arstechnica.com/information-technology/2015/05/sourceforge-grabs-gimp-for-windows-account-wraps-installer-in-bundle-pushing-adware/),
but other than those two minor niggles it's been a breeze. And, wonderfully,
Skim provides two (excellent) options for reloading. First, it can
reload (without scrolling to the beginning) on a change in the underlying
document. If you've already got your own editing setup, this is probably the way
to go. Otherwise, if you follow the rest of the instructions here, you can use
the scripting abilities of Skim. You're able to call it with pretty simple hooks
that can have it reload and focus on a particular point on the page, so it
scrolls to the page you've just edited (to be honest this is a little
hit-and-miss when it comes to diagrams, but by and large it works well).

For non-mac people, I've heard both
[zathura](https://pwmt.org/projects/zathura/) and
[Okular](https://okular.kde.org/) provide similar functionality. The next
section, which will go through editor integration, apparently will work
out-of-the-box with them (although I haven't tried).

# The Editor
