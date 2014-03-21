#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          racket/list
          redex/private/enumerator
          scribble/core
          "enum-util.rkt")

We represent enumerations as bijections between a the natural
numbers (or a prefix of them) and a set of terms. Concretely,
our enumerations are triples or a function that encodes a term as a
natural number, a function that decodes a natural number into a
term, and a size.

To get started, we build a few enumerators by directly
supplying encode and decode functions, e.g., @racket[nats/e]
using the identity as both encoding and decoding functions.

In general, we want to avoid working directly with the
functions because we must manually verify that the functions
form a bijection. It is more convenient and less error-prone to
instead use a combinator library to construct enumerations.

Our first combinator, @racket[fin/e] builds a finite enumeration 
from its arguments, so @racket[(fin/e 1 2 3 "a" "b" "c")] is
an enumeration with the six given elements.

The next combinator is the pairing operator 
@racket[cons/e], that takes two enumerations and returns an
enumeration of pairs of those values. If one of the
enumerations is finite, the bijection loops through the
finite enumeration, pairing each with an element from the
other enumeration. If both are finite, we loop through the
one with lesser cardinality. This corresponds to taking the
quotient with remainder of the index with the lesser size.

Infinite enumerations require more care. If we
imagine our sets as being laid out in an infinite table,
this operator zig-zags through the table to enumerate all
pairs:
@centered{@pair-pict[]}
which means that @racket[(cons/e nats/e nats/e)]'s
first @racket[12] elements are
@enum-example[(cons/e nats/e nats/e) 12]

Generalizing pairs to n-ary tuples is not simply a matter
of combining pairs together in an arbitrary way. 
In particular, here are two different ways to make
4-tuples of natural numbers:
@(tabular (list (list (codeblock unfair-exp)
                      (codeblock fair-exp))))

After enumerating @code{@(number->string num-enumerated)}
elements, the left-hand one has seen
@max-unfair in one component but only @min-unfair in
another, whereas the right-hand one has seen at most either
@min-fair or @max-fair in all components.

Another combinator is the disjoint union
operator, @racket[disj-sum/e], that takes two or more
enumerators and predicates to distinguish between their
elements. It returns an enumeration of their union. The
resulting enumeration alternates between the input
enumerations, so that if given @racket[n] infinite
enumerations, the resulting enumeration will alternate
through each of the enumerations every @racket[n] numbers:
@enum-example[(disj-sum/e (cons nats/e number?)
                          (cons (cons/e nats/e nats/e) pair?))
              12]

The @racket[disj-sum/e] enumerator also has to be fair and
to account for finite enumerations. So, for example, this
enumeration:
@racketblock[(disj-sum/e (cons (fin/e 'a 'b 'c) symbol?)
                         (cons nats/e number?)
                         (cons (fin/e "x" "y") string?))]
has to cycle through the finite enumerations until they
are exhausted before continuing with the rest of the natural
numbers:
@enum-example[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                          (cons nats/e number?)
                          (cons (fin/e "x" "y") string?))
              16]
In general, this means that @racket[disj-sum/e] must track the
ranges of natural numbers when each finite enumeration is exhausted
to compute which enumeration to use for a given index.

We provide a fixed-point combinator for
recursive enumerations:
@racket[fix/e : (enum → enum) → enum]
For example, we can construct an enumerator
for lists of numbers:
@racketblock[(fix/e (λ (lon/e)
                      (disj-sum/e (cons (const/e null)
                                        null?)
                                  (cons (cons/e nats/e lon/e)
                                        cons?))))]
and here are its first @racket[12] elements:
@enum-example[(fix/e (λ (lon/e)
                        (disj-sum/e (cons (const/e null) null?)
                                    (cons (cons/e nats/e lon/e) cons?))))
               12]
A call like @racket[(fix/e f)] enumerator 
calls @racket[(f (fix/e f))] to build the enumerator,
but it waits until the first time encoding or decoding 
happens before computing it. This means that a use of
@racket[fix/e] that is too eager, e.g.:
@racket[(fix/e (lambda (x) x))] will fail to terminate.
Indeed, switching the order of the arguments to @racket[disj-sum/e]
in the above example also produces an enumeration
that fails to terminate when decoding or encoding happens.

Our combinators rely on statically knowing the
sizes of their arguments, but in a recursive enumeration
this is begging the question. Since it is not possible to
statically know whether a recursive enumeration uses its
parameter, we leave it to the caller to determine the
correct size, defaulting to infinite if not specified.

To build up more complex enumerations, it is useful to be able to 
adjust the elements of an existing enumeration. We use @racket[map/e] 
which composes a bijection between any two
sets with the bijection in an enumeration, so we can for example construct 
enumerations of natural numbers that start at some point beyond zero:
@racketblock/define[(define (nats-above/e i)
                      (map/e (λ (x) (+ x i))
                             (λ (x) (- x i))
                             nats/e))]

Also, we can exploit the bijection to define the @racket[except/e]
enumerator. It accepts an element and an enumeration, and returns one
that doesn't have the given element. For example, the first
18 elements of @racket[(except/e nats/e 13)] are
@enum-example[(except/e nats/e 13) 18]
The encoder for @racket[except/e] simply decodes the
given element and then either subtracts one before
passing the natural number along (if it is above the 
given exception) or does (if it isn't). The decoder uses
similar logic.

One important point about the combinators used so far: the
decoding function is linear in the number of bits in the
number it is given. This means, for example, that it takes only
a few milliseconds to compute the
@(element (style "relax" '(exact-chars))
          '("\\(2^{100,000}\\)"))th element
in the list of natural number enumeration given above.

Our next combinator @racket[dep/e] doesn't have this property.
It accepts an enumerator and a function from elements to enumerators
and it enumerates pairs of elements where
the enumeration used for the second position in the pair depends
on the actual values in the first position in the pair.
For example, we can define an enumeration of ordered pairs 
(where the first position is smaller than the second) like this:
@racketblock[(dep/e nat/e (λ (i) (nats-above/e i)))]
Here are the first 12 elements of the enumeration:
@enum-example[(dep/e nats/e (λ (i) (nats-above/e i)))
              12]
The @racket[dep/e] combinator assumes that if any of the enumerations
produced by the dependent function are infinite then all
of them are. 
The implementation of @racket[dep/e] has three different
cases, depending on the cardinality of the enumerators it
receives. If all of the enumerations are infinite, then it
is very similar to the @racket[cons/e] enumerator, but just
using the dependent function to build the enumerator to select
from for the second element of the pair. Similarly, if the
second enumerations are all infinite but the first one is finite,
then @racket[dep/e] can use quotient and remainder to compute
the indicies to supply to the given enumerations when decoding.

The troublesome case is when the 
second enumerations are all finite. In that case, we
think of the second component of the pair being drawn from
a single finite enumeration that consists of all of the
finite enumerations, one after the other. Unfortunately,
in this case, the @racket[dep/e] enumerator must compute
all of the enumerators for the second component as soon
as a single (sufficiently large) number is passed to decode.
