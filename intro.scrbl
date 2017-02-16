#lang scribble/base
@(require scriblib/footnote
          "util.rkt"
          "unfair-pairing.rkt"
          "cite.rkt")

@title{Introduction}

In the past few years a number of different libraries have
appeared that provide generic ways to build bijections
between data structures and the natural numbers to support
property-based testing. First was
Feat for Haskell in
2012@note{@url{https://hackage.haskell.org/package/testing-feat}},
then SciFe for Scala in
2014@note{@url{http://kaptoxic.github.io/SciFe/}}, and
we released @tt{data/enumerate} as part of Racket in
2015.@note{@url{http://docs.racket-lang.org/data/Enumerations.html}}

These libraries are efficient, providing the
ability to extract the @texmath{2^{100}}-th element of an
enumeration of a data structure in milliseconds. What they
lack, however, is a mathematically precise notion of the
quality of their combinators. To be concrete, consider the pairing
combinator, which all of the libraries provide.
It accepts
two enumerations and returns an enumeration of pairs of its inputs.
There are many ways to
build such an enumeration, based on the many ways
to write a bijection between the natural numbers and
pairs of natural numbers. One such function is given by 
@texmath[bad-nn->n-string]. This is a bijection (the inverse
simply counts the number of times that 2 is a factor of its
input to separate the @texmath{x} and @texmath{y} parts) that is easy to
explain and efficient, taking logarithmic time in the result
to compute in both directions. It is
a poor choice for an enumeration library, however, because it
explores @texmath{x} coordinate values much more quickly
than the @texmath{y} coordinate. Indeed, in the first
@(add-commas bad-howmany) pairs, the @texmath{x} coordinate
has seen @(add-commas bad-max-x) but the biggest @texmath{y} coordinate
seen is @(add-commas bad-max-y).

This paper offers a criterion called @emph{fairness}
that classifies enumeration combinators, rejecting the one
in the previous paragraph as unfair and accepting
ones based on the standard Cantor bijection and many others,
including ones whose inverses are easier to compute in the
@texmath{n}-tuple case (as explained later). Intuitively, a
combinator is fair if indexing deeply into the result of the
combinator goes equally deeply into all the arguments to the
combinator.

The motivation for developing these enumeration
libraries is bug-finding. Accordingly, we tested our concept
of fairness via an empirical study of the capability of
enumeration libraries to find bugs in formal models of type
systems and operational semantics in
Redex@~cite[run-your-research]. We used our existing benchmark suite of 50
bugs and compared the bug/second rate with three different
generators. Two of the generators are based on a bijection
between the expressions of the language and the natural
numbers: one enumerates terms in order and the other
selects a random (possibly large) natural number and uses
that with the bijection. The third is an
existing, ad hoc random generator that's been tuned for
bug-finding in Redex models for more than a decade.

Our results show that fair in-order enumeration and ad hoc generation
have complementary strengths, and that selecting a random
natural number and using it with a fair enumeration is always
slightly worse than one of the other two choices. We also replaced
fair combinators with unfair ones and show that the bug-finding
capabilities become significantly worse.

In the next two sections, we discuss how testing
and enumeration fit together and then
introduce enumeration libraries, using
the Racket-based library to make the introduction
concrete.
In @secref["sec:fair-informal"], we give an
intuition-based definition of fairness and
in @secref["sec:fair-combinators"] discuss our
@texmath{n}-ary combinators, whose designs are motivated by fairness.
@Secref["sec:fair-formal"] has a formal definition of fairness
and proofs showing that our combinators are fair and that a commonly-used
combinator is unfair. Our
evaluation of the different random generation strategies is
discussed in @secref["sec:evaluation"]. The next two sections
discuss related work and future work;
section @secref["sec:conclusion"] concludes.
Several places in the paper mention supplementary material; it
is included in our submission and also available at
@url["http://www.eecs.northwestern.edu/~robby/tmp/jfp-enum/"]
