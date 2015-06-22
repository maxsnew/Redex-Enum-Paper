#lang scribble/base
@(require scriblib/footnote
          "util.rkt"
          "unfair-pairing.rkt"
          "cite.rkt")

@title{Introduction}


In the past few years a number of different libraries have
appeared that provide generic ways to build bijections
between data structures and the natural numbers. First was
Feat for Haskell in
2012@note{https://hackage.haskell.org/package/testing-feat},
then SciFe for Scala in
2014@note{http://kaptoxic.github.io/SciFe/}, and
@tt{data/enumerate} for Racket this
year.@note{http://docs.racket-lang.org/data/Enumerations.html}

These libraries are all efficient, generally providing the
ability to extract the @texmath{2^{100}}-th element of an
enumeration of a data structure in milliseconds. What they
lack, however, is a mathematically precise notion of the
quality of their combinators. To be concrete, all of
these libraries provide a pairing combinator that accepts
two enumerations and returns an enumeration of pairs of the
elements of the given enumeration. There are many ways one
might build such an enumeration, based on the many ways that
one might write a bijection between the natural numbers and
pairs of natural numbers. One such function is given by 
@texmath[bad-nn->n-string]. This is a bijection (the inverse
simply counts the number of times that two is a factor of the
input to separate the ``x'' and ``y'' parts) that is easy to
explain and efficient (taking logarithmic time in @texmath{n})
to compute in both directions. It is
a poor choice for an enumeration library, however, because it will
explore ``x'' coordinate values much more quickly
than the ``y'' coordinate. Indeed, in the first
@(add-commas bad-howmany) pairs, the ``x'' coordinate
has seen @(add-commas bad-max-x) but the biggest ``y'' coordinate
seen is @(add-commas bad-max-y).

In this paper, we offer a criterion called @emph{fairness}
that classifies enumeration combinators. Intuitively, a
combinator is fair if indexing deeply into the result of the
combinator goes equally deeply into all the arguments to the
combinator. Our definition rules out a pairing operation
based on the function above, but accepts one based on the
standard Cantor bijection and many others, including ones
whose inverses are easier to compute in the n-tuple case (as
explained later).

The motivation for the developing these enumeration
libraries is bug-finding. Accordingly we tested our concept
of fairness via an empirical study of the capability of
enumeration libraries to find bugs in formal models of type
systems and operational semantics in
Redex@~cite[run-your-research]. We built a benchmark suite of 50
bugs (based on our experience writing Redex models and the
experience of others mined from git repositories of Redex
models) and compare the bug/second rate with three different
generators. Two of the generators are based on a bijection
between the expressions of the language and the natural
numbers: one enumerates terms in order and the other that
selects a random (possibly large) natural number and uses
that with the bijection between, and the third is an
existing, ad hoc random generator that's been tuned for
bug-finding in Redex models for more than a decade.

As a baseline comparison, our
results show that fair in-order enumeration and ad hoc generation
have complementary strengths, and that selecting a random
natural and using it with a fair enumeration is almost always
slightly worse than one of the other two choices. We also replaced
fair combinators with unfair ones and show that the the bug-finding
capabilities become significantly worse.

The next section introduces enumeration libraries, focusing
on the Racket-based library to make the introduction
concrete. Then, in @secref["sec:fair-informal"] we give an
intuition-based definition of fairness and discuss our
our new n-tuple combinator, who design is motivated by fairness.
We follow up in 
@secref["sec:fair-formal"] with a formal definition of fairness
and proofs that our combinators are fair and that a commonly used
combinator is unfair. Our
evaluation of the different random generation strategies is
discussed in @secref["sec:evaluation"]. The next two
sections discuss related and future work, and the last section concludes.
