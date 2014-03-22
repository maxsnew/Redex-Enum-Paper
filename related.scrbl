#lang scribble/base

@(require "cite.rkt")

@;{

   related work:

- need to shout out to nice studies: 
  - "Heuristics for Scalable Dynamic Test Generation"
  - smallcheck paper
  - early random testing studies


}


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

@;{
@section{Related Problems}

Enumeration is closely tied to other problems: counting, ranking and
generation.

- On counting untyped lambda terms (Lescanne)
- Lambda-terms of bounded unary height (Bodini, Gardy)
- Counting and generating lambda terms (Grygiel and Lescanne)

Counting answers the question: given some parameter, how many elements
of a set are there? For instance, how many 32bit RGB colors are there?
Or, most closely to our problem domain: how many typed lambda terms
with fewer than five variables are there? There are many approaches to
this problem (XXX) some of which could be seen as restricted versions
of the enumeration approach we employ.

- Binary lambda calculus and combinatory logic (Tromp)
- Others from Tarau's paper

Ranking, or numbering, is the problem of injecting objects into the
naturals without the constraint that decoding is uncomputable,
efficient, or forms a bijection.

Generation can be divided into two approaches: exhaustive or
non-exhaustive. 

- Counting and generating lambda terms (Grygiel and Lescanne)

- Generic algorithms for the generation of combinatorial
objects (Martinez)

- The Art of Computing Programming, Volume 4, Fascicle 4: Generating All
Trees-History of Combinatorial Generation (Knuth)

- The New QuickCheck for Isabelle: Random, Exhaustive, and Symbolic
Testing Under One Roof

Exhaustive generation is a process that generates all possible
instances of some combinatorial structure. This corresponds closely to
the ``list'' view of enumeration, which could be turned into
the ``function'' view by taking the index into the enumeration as the
encoding, except that there's no guarantee of ordering or other regime
to make injection efficient (decoding does not have this problem, of
course.) The New QuickCheck for Isabelle implements an interesting
modification of the ``list'' view by representing the potentially
infinite stream as a function that accepts a reader of the stream,
i.e. the continuation of [next], and calls it for each value,
up to some bound.

- Efficient Random Sampling of Binary and Unary-Binary Trees via
Holonomic Equations (Bacher, Bodini, Jacquot)

- Boltzmann Samplers for the random generation of combinatorial structures (Duchon)

- Fast and Sound Random Generation for Automated Testing and
Benchmarking in OCaml

Non-exhaustive generation is typically randomized and delivers
efficient algorithms for sampling from some neighborhood of elements,
where the neighborhood is typically a size bound, i.e. a uniform
distribution over lambda terms with around five variables. The most
common approach for this is with Boltzmann samplers, as these have
application in physics.
}

@section{Automatic Checking}

- Automatic Proof and Disproof in Isabelle/HOL

XXX: No new enumeration methods, primarily cites QuickCheck and makes
claims about its usefulness

- Fast and Sound Random Generation for Automated Testing and
Benchmarking in OCaml

XXX Boltzmann models mentioned above, but we should talk about their
claims of utility here

- SmallCheck and Lazy SmallCheck: Automatic Exhaustive Testing for Small
Values

XXX "List" perspective is discussed above and Feat paper goes into
details on the methodology. Herein we should talk about case study

- Testing an Optimising Compiler by Generating Random Lambda Terms

XXX Ad-hoc generation method, very similar to our grammar based
approach. Does not enumerate

- The New QuickCheck for Isabelle: Random, Exhaustive, and Symbolic
Testing Under One Roof

XXX Does not enumerate, in the sense of mapping to integers, instead
they take the "list" approach, but unravel the lazy stream into a
continuation-based representation. makes empirical claims
