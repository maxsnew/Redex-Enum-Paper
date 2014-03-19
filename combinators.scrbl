#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          "util.rkt")

An enumeration of is a bijection between a subset of the natural numbers
and a countable set of terms. We represent this as a function that encodes
a term as a natural number, a function to decode a natural number into a term
and a (possibly infinite) size of the set.

We can now manually construct an enumeration from a hand-written bijection, 
but then we must manually verify that our function is bijective. It is more
convenient and less error-prone to instead use a combinator library to construct
enumerations that are bijective by construction.

It is convenient to build off of a few primitive enumerations. The empty
enumeration @(racket empty/e) consisting of no elements, the identity
enumeration @(racket nats/e) of the natural numbers themselves and
a function @(racket from-list/e)
that constructs an enumeration from any finite list (assumed
to have no duplicates). We will show examples using the @(racket approximate)
function that returns a prefix of an enumeration as a list.
@(interact (decode empty/e 0))
@(interact (approximate nats/e 10))
@(interact (decode (from-list/e '(a b c)) 1))
@(interact (encode (from-list/e '(a b c)) 'b))

One fundamental combinator is the pairing operator @(racket cons/e), that takes 2 enumerations
and returns an enumeration of pairs of those values. If one of the enumerations
is finite, the bijection loops through the finite enumeration, pairing each with
an element from the other enumeration. If both are finite, we loop through the
one with lesser cardinality. This corresponds to taking the quotient with
remainder of the index with the lesser size.

However an infinite enumeration requires more care. If we imagine our sets
as being laid out in an infinite table, this operator zig-zags through the
table to enumerate all pairs, so that the sum of the encoded values in each
side of the pair increases with the index. To find the proper depth, we must
find the smallest so-called "triangle number", the partial sums of the infinite
sum of natural numbers.

@(interact (approximate (cons/e nats/e nats/e) 10))
@; TODO: show the triangle numbers?

@; TODO: show examples?
Another fundamental combinator is the disjoint union operator @(racket disj-sum/e)
that takes two or more enumerators and predicates to distinguish between their elements and 
returns an enumeration of their union. The resulting enumeration alternates between the 
input enumerations, so that if given @(racket n) infinite enumerations, the resulting
enumeration will alternate through each of the enumerations every @(racket n)
numbers.

@(interact (approximate 
            (disj-sum/e (cons nats/e number?)
                        (cons string/e string?)
                        (cons (many/e nats/e) list?))
            12))
@;TODO: talk about finite case?

@; TODO: fix/e and thunk/e
Recursive enumerations can be easily constructed with a fix-point combinator,
though in general a more extensible method is needed. We implement mutual recursion
using references and a primitive combinator that delays evaluation.
But how do we determine the size of a recursive enumeration? Our combinators rely
on statically knowing the sizes of their arguments, but in a recursive enumeration
this is begging the question! Since it is not possible to statically know
whether a recursive enumeration uses its parameter, we leave it to the caller
to determine the correct size.
With pairing, alternation and recursion, we have the building blocks of algebraic
data types. It is now straightforward to define an enumeration of lists of a 
given type.

An advantage of encoding both sides of the bijection that defines an enumeration
is the ability to filter individual elements. The @(racket except/e) combinator
takes an enumeration and a value in that enumeration and returns an enumeration
without the given element.
Allowing us to easily write a function that enumerates non-empty lists.
@(racketblock
  (define (many1/e e)
    (except/e e '())))
@(interact (approximate (many/e nats/e) 6))
@(interact (approximate (many1/e nats/e) 5))

@; TODO: examples of other derived combinators?
@; map/e with multiple arguments

@; dep/e