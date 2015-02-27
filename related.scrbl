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
First, our n-ary enumerations are fair (not just the binary ones).
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

@citet[feat]'s Feat is a system for enumeration that distinguishes
itself from ``list'' perspectives on enumeration by focusing on the
``function'' perspective. We also use the ``function'' perspective. 
While our approach is closer to Tarau's, we share support for
finite sets with Feat, but are distinct from Feat in our support for
dependent pairing and fairness. Also, Feat has only one half of the
bijection and thus cannot support @racket[except/e] (and thus cannot
easily support identifiers that contain all strings, except without a
small set of keywords like we need for Redex).  

It is tempting to think of Feat as supporting fairness because of the
way it partitions the values to be enumerated into finite subsets,
in such a way that the element of each finite subset has a fixed number
of constructor. Unfortunately, this is not the same as fairness because
Feat inserts ``dummy'' constructors in a way that makes all pairing
operations be binary pairs. Put another way, it is not possible to 
fairly enumerate a three-tuple of natural numbers using Feat. Feat
can enumerate such tuples, but it effectively
gives you an enumeration of nested pairs which is, as discussed in 
@secref["sec:fair-informal"], unfair.

@citet[scife] is similar to Feat, but with
the addition of a dependent combinator. Like Feat, it does not support
@racket[except/e] or fairness.

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

@citet[bit-monad-transformers] explicitly discuss fairness in the
context of logic programming, but talk about it in the specific cases
of fair disjunction and fair conjunction, but they do not have a
unification of these two different types of fairness, nor do they have
a concept of n-ary fair operators for n > 2.

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
distribution like ours.

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
