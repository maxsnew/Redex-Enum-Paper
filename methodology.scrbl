#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          "util.rkt"
          scriblib/figure
          scriblib/footnote
          (only-in pict scale)
          plot/pict 
          (only-in redex/private/generate-term pick-an-index))

@title[#:tag "sec:methodology"]{Methodology}

Our case study compares three types of test-case generation
using a set of buggy models. Each model and bug is equipped
with a property that should hold for every term (but doesn't
due to the bug) and three functions that generate terms, one
for each of the different strategies. The three test-case
generation strategies we evaluate (described below) are
in-order enumeration, random selection from a uniform
distribution, and ad hoc random generation.

For each bug and generator, we run a script that repeatedly
asks for terms and checks to see if they falsify the property.
As soon as it finds a counter example to the property, it reports
the amount of time it has been running. The script runs until
the uncertainty in the average becomes acceptably small or
until 24 hours elapses, whichever comes first.

We ran our script on one of two identical 64 core AMD
machines with Opteron 6274s running at 2,200 MHz with a 2 MB
L2 cache. Each machine has 64 gigabytes of memory. Our
script runs each model/bug combination sequentially,
although we ran multiple combinations at once in parallel.

We used the unreleased version 6.0.0.5 of Racket (of which
Redex is a part); more precisely the version at git commit
@tt{a7d6809243},@note{@url{https://github.com/plt/racket/commit/a7d6809243}}
except for the in-order generation of the @bold{rvm} model 
(discussed in @secref["sec:rvm"]), because we recently
discovered a bug in that model's in-order generator that
could affect its running time. 
They were run from a slightly different
version of Racket, namely commit @tt{da158e6d95}. The only
other difference between the two versions are some
improvements to Typed Racket that are unlikely to affect our
results.

For the in-order enumeration, we simply indexed into the
decode functions (as described in @secref["sec:enum"]),
starting at zero and incrementing by one each time. 

For the random selection from the uniform distribution, we
need a mechanism to pick a natural number. To do this, we
first pick an exponent @raw-latex|{$i$}| in base 2 from the
geometric distribution and then pick uniformly at random an
integer that is between @raw-latex|{$2^{i-1}$}| and 
@raw-latex|{$2^i$}|. We repeat this process three times for
each number and then take the largest -- this helps make
sure that the numbers are not always small.

The random-selection results are quite sensitive to the
precise probability of picking the zero exponent (the
parameter of the geometric distribution). To maximize that
method's chances of success we picked a value that produced
terms that have depth between 2 and 3 on average. This seems
to give that approach the best chance of success.

For the ad hoc random generation, we use Redex's existing 
random generator@~cite[sfp2009-kf]. It has been tuned
based on our experience programming in Redex, but not
recently. The most recent change to it was a bug fix in
April of 2011 and the most recent change that affected
the generation of random terms was in January of 2011,
both well before we started the current study. This
generator, which is based on the method of recursively
unfolding non-terminals, is parameterized over the
depth at which it attempts to stop recurring. We chose
a value of 5 for this depth since that seemed to be the most 
successful, as above. This produces terms of a similar 
size to those of the random-selection generator, although 
the distribution is different.
