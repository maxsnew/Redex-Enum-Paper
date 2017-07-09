#lang scribble/base
@(require "cite.rkt" "util.rkt" scribble/manual)

@title[#:tag "sec:related-work"]{Related Work}

The related work divides into two categories: papers about
enumeration and papers with studies about random testing.

@section{Bijective Enumeration Methods}

The SciFe library for Scala@~cite[scife scife2] is most similar to our library,
but it has only one half of the bijection so it does
not support @racket[except/e]. It has fair binary pairing
and alternation combinators, but no @texmath{n}-ary fair combinators.
Its combinators use the same bijections as the mildly unfair
combinators discussed in @secref["sec:evaluation"].
Its pairing operation is based on the Cantor pairing
function, meaning that computing the @texmath{n}-ary fair version of
it is expensive, as discussed in 
@secref["sec:fair-informal"]. These differences and the lack
of fairness aside, the
technical details of the implementation are very similar and
our library shares all of the strengths and weakness of their library.

@citet[compact-serialization-of-prolog-terms]'s work on bijective encoding schemes for 
Prolog terms is also
similar to ours. We differ in three main ways. 
First, our @texmath{n}-ary enumerations are fair (not just the binary ones).
Second, our enumerations deal with enumeration of finite sets wherever
they appear in the larger structure. This is complicated because it
forces our system to deal with mismatches between the cardinalities of
two sides of a pair: for instance, the naive way to implement pairing
is to give odd bits to the left element and even bits to the right
element, but this cannot work if one side of the pair, say the left,
can be exhausted as there will be arbitrarily numbers of bits that
do not enumerate more elements on the left. Third, we have a
dependent pairing enumeration that allows the right element of a pair
to depend on the actual value produced on the left. Like finite sets,
this is challenging because of the way each pairing of an element on
the left with a set on the right consumes an unpredictable number of
positions in the enumeration.

@citet[feat]'s Feat is a system for enumeration that
distinguishes itself from ``list'' perspectives on
enumeration by focusing on the ``function'' perspective like
we do. Unlike our approach, however, Feat's enumerations are
not just bijective functions directly on naturals, but
instead a sequence of finite bijections that, when strung
together, combine into a bijection on the naturals. In other
words, the Feat combinators get more information from their
inputs than ours do, namely a partitioning of the naturals
into consecutive finite subsets. This additional information
means that our precise, technical definition of fairness
does not apply directly to Feat's combinators. The intuition
of fairness, however, does apply and Feat's pairing
combinator is fair in the sense that its output reaches
equilibrium infinitely often. Indeed, it reaches equilibrium
at the end of each of the parts in the result. The code
given in the paper for the pairing and alternation
combinators are @texmath{f}-fair with equilibrium points
that have the same asympototic complexity as our binary
combinators. In the implementation, however, they use a
binary representation, not a unary representation of
naturals, which makes the distance between consecutive
equilibrium points double at each step, making the
equilibrium points exponentially far apart.

@citet[every-bit-counts] take a different approach to something like
enumeration, viewing the bits of an encoding as a sequence of messages
responding to an interactive question-and-answer game. This method also 
allows them to define an analogous dependent combinator.
However, details of their system show that it is not well suited to
using large indexes. In particular, the strongest proof they have is that if a
game is total and proper, then ``every bitstring encodes some value or
is the prefix of such a bitstring''. This means, that even for total,
proper games there are some bitstrings that do not
encode a value. As such, it cannot be used efficiently to enumerate all
elements of the set being encoded.

@section{Testing Studies}

Our empirical evaluation is focused on the question of
fairness, but it also sheds some light on the relative
quality of enumeration and random-based generation
strategies.

Even though enumeration-based testing methods have been
explored in the literature, there are few studies that
specifically contain empirical studies comparing random
testing and enumeration. One is in @citet[small-check]'s original paper on
SmallCheck. SmallCheck is an enumeration-based testing
library for Haskell and the paper contains a comparison with
QuickCheck, a Haskell random testing library.
Their study is not as detailed as ours; the paper does not
say, for example, how many errors were found by each of the
techniques or in how much time, only that there were two 
found by enumeration that were not found
randomly. The paper, however, does conclude 
that ``SmallCheck, Lazy SmallCheck and QuickCheck are
complementary approaches to property-based testing in Haskell,''
a stance that our experiment also supports (but for Redex).

@citet[one-roof] compares a single tool that supports both
random testing and enumeration against a tool that reduces
conjectures to boolean satisfiability and then uses a solver.
The study concludes that the two techniques complement each other.
Neither study compares selecting randomly from a uniform
distribution like ours.

@citet[generating-random-lambda-terms]'s work is similar in spirit to
Redex, as it focuses on testing programming languages. Pałka builds
a specialized random generator for well-typed terms that found
several bugs in GHC, the premier Haskell compiler.
Similarly, 
@citet[finding-and-understanding-bugs-in-c-compilers]'s 
work 
also presents a test-case generator tailored to testing programming 
languages with complex well-formedness constraints.
C. @citet[fuzzing-unix-utils] designed a random generator for streams
of characters with various properties (e.g. including nulls or not, 
to include newline characters at specific points) and used it
to find bugs in Unix utilities.
@;{
In surveying related work, we noticed that despite an early,
convincing study on the value of random
testing@~cite[an-evaluation-of-random-testing]
and an early influential paper@~cite[fuzzing-unix-utils], there 
seems to be a general impression that random testing is a poor choice for
bug-finding. For example, 
@citet[dart] and
@citet[contract-driven-testing-of-javascript-code] 
both dismiss random testing using the relatively simple example:
@raw-latex{$\forall x, x * 2 \neq x + 10$} as support, suggesting that
it is hard for random testing to find a counterexample to
this property. When we run this example in 
Quickcheck@~cite[quickcheck]
giving it 1000 attempts to find a counterexample, it finds it
about half of the time, taking on average about 400 attempts 
when it succeeds.
Redex's random generator does a little bit better, finding it
nearly every time, typically in about 150 attempts.
Not to focus on a single example 
@citet[isabelle-testing] discuss this buggy
property (the last @racket[xs] should be @racket[ys]):
@racketblock[nth (append xs ys) (length xs+n) = nth xs n]
saying that
“[r]andom testing typically fails to find the counterexample, even 
with hundreds of iterations, because randomly chosen values for 
@racket[n] are almost always out of bounds.”

This property is easier for both Quickcheck and Redex,
taking, on average, 4 attempts for Quickcheck and 5 for Redex
to find a counterexample.

Of course, the reason Quickcheck and Redex find these bugs
is because the distribution they use for integers is biased
towards small integers, which is natural as those integers
are usually more likely to be interesting during testing.
}