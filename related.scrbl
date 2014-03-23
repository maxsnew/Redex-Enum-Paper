#lang scribble/base
@(require "cite.rkt")

The related work divides into two categories: papers 
about enumeration and papers with studies about
random testing.

@section{Enumeration Methods}

@citet[bijective-term-encodings]'s work on bijective encoding schemes for 
Prolog terms is most
similar to ours. However, we differ in two main ways. First, our
enumerators deal with enumeration of finite sets wherever
they appear in the larger structure. This is complicated because it
forces our system to deal with mismatches between the cardinalities of
two sides of a pair: for instance, the naive way to implement pairing
is to give odd bits to the left element and even bits to the right
element, but this cannot work if one side of the pair, say the left,
can be exhausted as there will be arbitrarily numbers of bits that
do not enumerate more elements on the left. Second, we have a
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
Feat, but are distinct from Feat in our support for dependent pairing,
which can be easily used to implement what Feat refers to
as ``invariants'' (although not efficiently).

@citet[every-bit-counts] take a different approach to something like
enumeration, viewing the bits of an encoding as a sequence of messages
responding to an interactive question-and-answer game. The crucial
insight in this perspective is that the questioner may have its own
memory to help it avoid asking ``silly'' questions, such as whether a
term is a number when the type system rules out a number at that
position in the larger term structure. This aspect of their system,
which is crucial in what they call dependent composition, is the same
as our dependent pairing.

However, details of their system show that it is not an enumeration
system. In particularly, the strongest proof they have is that if a
game is total and proper, then ``every bitstring encodes some value or
is the prefix of such a bitstring''. This means, that even for total,
proper games there are some bitstrings that do not
encode a value. As such, it cannot be used to enumerate all
elements of the set being encoded. Furthermore, they show that many
useful games are non-proper and must be converted into proper games by
filtering a non-proper game: enumerating all possible elements and
removing those that do not match a predicate. This rejection-based
approach to generating well-typed terms, for example, is costly; 
as discussed in detail, for instance, in the paper
on Feat. Our system has a similar problem with dependent pairs where
to decode an element from the n+1-st set, you must have a
count for each of the prior n sets. However, when these
counts are predictable, they need no be constructed; and when they
have been previously computed, they can be reused (and our
implementation caches them).

@section{Testing Studies}

We are aware of only one other studies that specifically compares
random testing and enumeration, namely in
@citet[small-check]'s original paper on SmallCheck. SmallCheck is an
enumeration-based testing library for Haskell and the paper 
contains a comparison with QuickCheck, Haskell random testing 
library.

Their study is not as in-depth as ours; the paper does not
say, for example, how many errors were found by each of the
techniques or in how much time, only that there were two 
errors that were found by enumeration that were not found
by random testing. The paper, however, does conclude 
that ``SmallCheck, Lazy SmallCheck and QuickCheck are
complementary approaches to property-based testing in Haskell,''
a stance that our study supports (but for Redex).

@citet[one-roof] compares a single tool that supports both
random testing and enumeration against a tool that reduces
conjectures to boolean satisfiability and then uses a solver.
The study concludes that the two techniques complement each other.

Neither of the studies compare selecting randomly from a uniform
distribution like ours does.

@citet[generating-random-lambda-terms]'s work is similar in spirit to
Redex, as it focuses on testing programming languages. Pałka builds
a specialized random generator for well-typed terms that found
several bugs in GHC, the premier Haskell compiler.
Similarly, @citet[finding-and-understanding-bugs-in-c-compilers]'s work 
also presents a test-case generator tailored to testing programming 
languages with complex well-formedness constraints, but this time
C. 

Both of these papers provide empirical evidence that random generation
techniques that do not sample from a uniform distribution can be
highly successful at finding bugs.
