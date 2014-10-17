#lang scribble/base
@(require "cite.rkt" "util.rkt" scribble/manual)

@title[#:tag "sec:related-work"]{Related Work}

The related work divides into two categories: papers 
about enumeration and papers with studies about
random testing.

@section{Enumeration Methods}

@citet[bijective-term-encodings]'s work on bijective encoding schemes for 
Prolog terms is most
similar to ours. However, we differ in three main ways. 
First, our n-ary enumerators are fair (not just the binary ones).
Second, our enumerators deal with enumeration of finite sets wherever
they appear in the larger structure. This is complicated because it
forces our system to deal with mismatches between the cardinalities of
two sides of a pair: for instance, the naive way to implement pairing
is to give odd bits to the left element and even bits to the right
element, but this cannot work if one side of the pair, say the left,
can be exhausted as there will be arbitrarily numbers of bits that
do not enumerate more elements on the left. Third, we have a
dependent pairing enumerator that allows the right element of a pair
to depend on the actual value produced on the left. Like finite sets,
this is challenging because of the way each pairing of an element on
the left with a set on the right consumes an unpredictable number of
positions in the enumeration.

@citet[feat]'s 
Feat is a system for enumeration that distinguishes itself from
``list'' perspectives on enumeration by focusing on the ``function''
perspective. We use the ``function'' perspective as well. While our
approach is closer to Tarau's, we share support for finite sets with
Feat, but are distinct from Feat in our support for dependent pairing
and fairness. Also, Feat has only one half of the bijection and thus
cannot support @racket[except/e] (and thus cannot easily support
identifiers that contain all strings, except without a small set of keywords).
@citet[scife] is similar to Feat and, like Feat, does not support 
@racket[except/e] or fairness.

@citet[every-bit-counts] take a different approach to something like
enumeration, viewing the bits of an encoding as a sequence of messages
responding to an interactive question-and-answer game. 
However, details of their system show that it is not well suited to
using large indexes. In particular, the strongest proof they have is that if a
game is total and proper, then ``every bitstring encodes some value or
is the prefix of such a bitstring''. This means, that even for total,
proper games there are some bitstrings that do not
encode a value. As such, it cannot be used to enumerate all
elements of the set being encoded.

@citet[bit-monad-transformers] explicitly discuss fairness,
but have a much stricter notion than we do and one that is
not generalized to n-ary fair operators (neither do they
provide any n-ary fair operators).

@section{Testing Studies}

Although the focus of our paper is on the combinators and
fairness, the literature has few studies that specifically
compare random testing and enumeration. We are aware of only
one other, namely in @citet[small-check]'s original paper on
SmallCheck. SmallCheck is an enumeration-based testing
library for Haskell and the paper contains a comparison with
QuickCheck, Haskell random testing library.

Their study is not as in-depth as ours; the paper does not
say, for example, how many errors were found by each of the
techniques or in how much time, only that there were two 
errors that were found by enumeration that were not found
by random testing. The paper, however, does conclude 
that ``SmallCheck, Lazy SmallCheck and QuickCheck are
complementary approaches to property-based testing in Haskell,''
a stance that our experiment also supports (but for Redex).

@citet[one-roof] compares a single tool that supports both
random testing and enumeration against a tool that reduces
conjectures to boolean satisfiability and then uses a solver.
The study concludes that the two techniques complement each other.

Neither study compares selecting randomly from a uniform
distribution like ours does.

@citet[generating-random-lambda-terms]'s work is similar in spirit to
Redex, as it focuses on testing programming languages. Pałka builds
a specialized random generator for well-typed terms that found
several bugs in GHC, the premier Haskell compiler.
Similarly, 
@citet[finding-and-understanding-bugs-in-c-compilers]'s 
work 
also presents a test-case generator tailored to testing programming 
languages with complex well-formedness constraints, but this time
C. @citet[fuzzing-unix-utils] designed a random generator for streams
of characters with various properties (e.g. including nulls or not, 
to include newline characters at specific points) and used it
to find bugs in unix utilities.

Despite an early, convincing study on the value of random
testing@~cite[an-evaluation-of-random-testing]
and an early influential paper@~cite[fuzzing-unix-utils], there are other papers that
suggest that random testing is a poor choice for
bug-finding. For example, 
@citet[contract-driven-testing-of-javascript-code] write:
@a-quote{
“Spotting this defect requires the test case generator to 
guess a value for x such that x * 2 == x + 10 holds, 
but a random integer solves this equation with probability 
@raw-latex|{\(2^{-32}\)}|.”
}

When we run this example in 
Quickcheck@~cite[quickcheck]
giving it 1000 attempts to find a counterexample, it finds it
about half of the time, taking on average about 400 attempts 
when it succeeds.
Redex's random generator does a little bit better, finding it
nearly every time, typically in about 150 attempts.

Not to single out a single paper, @citet[dart] use the same
example and @citet[isabelle-testing] discuss this buggy
property (the last @racket[xs] should be @racket[ys]):
@racketblock[nth (append xs ys) (length xs+n) = nth xs n]
saying that
@a-quote{
“[r]andom testing typically fails to find the counterexample, even 
with hundreds of iterations, because randomly chosen values for 
@racket[n] are almost always out of bounds.”
}
This property is easier for both Quickcheck and Redex,
taking, on average, 4 attempts for Quickcheck and 5 for Redex
to find a counterexample.

Of course, the reason Quickcheck and Redex find these bugs
is because the distribution they use for integers is biased
towards small integers, which is natural as those integers
are usually more likely to be interesting during testing.

This paper is one of two papers submitted to ESOP that
discusses random testing in the context of Redex. The other
is entitled @italic{Making Random Judgments: Automatically
 Generating Well-Typed Terms from the Definition of a
 Type-System}. This paper has a less effective generator,
but one that applies to all Redex models. The
technical content is otherwise completely different.
