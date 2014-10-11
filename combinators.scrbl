#lang scribble/lncs

@(require scribble/manual
          scribble/eval
          racket/list
          redex/private/enumerator
          scribble/core
          "util.rkt"
          "enum-util.rkt")

@title[#:tag "sec:enum"]{Enumeration Combinators}

We represent enumerations as bijections between the natural
numbers (or a prefix of them) and a set of terms. Concretely,
our enumerations are triples of a function that encodes a term as a
natural number, a function that decodes a natural number into a
term, and a size.

To get started, we build a few enumerators by directly
supplying encode and decode functions, e.g., @racket[nat/e]
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
which means that @racket[(cons/e nat/e nat/e)]'s
first @racket[12] elements are
@enum-example[(cons/e nat/e nat/e) 12]

Generalizing pairs to n-ary tuples is not simply a matter
of combining pairs together in an arbitrary way. 
In particular, here are two different ways to make
4-tuples of natural numbers:
@(tabular (list (list (codeblock unfair-exp)
                      (codeblock fair-exp))))

After enumerating @code{@(number->string num-enumerated)} elements,
the left-hand one has seen @max-unfair in one component but only
@min-unfair in another, whereas the right-hand one has seen at most
either @min-fair or @max-fair in all components. We refer to the
right-hand version as being "fair" and always prefer fairness in our
implementations, because it appears to correspond to the uniformity
that is perceived as valuable with enumeration. In our experience,
most of the time the obvious version of an enumerator is not fair and
the details required to tweak it are non-intuitive. In this case, the
key insight to achieve fairness is to map the leaves of the enumerated
structure to the triangle numbers.

Another combinator is the disjoint union
operator, @racket[disj-sum/e], that takes two or more
enumerators and predicates to distinguish between their
elements. It returns an enumeration of their union. The
resulting enumeration alternates between the input
enumerations, so that if given @racket[n] infinite
enumerations, the resulting enumeration will alternate
through each of the enumerations every @racket[n] numbers.
For example, the following is the beginning of the disjoint
sum of an enumeration of natural numbers and an enumeration
of strings
@enum-example[(disj-sum/e (cons nat/e number?)
                          (cons string/e string?))
              14]

The @racket[disj-sum/e] enumerator also has to be fair and
to account for finite enumerations. So this
enumeration:
@racketblock[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                         (cons nat/e number?)
                         (cons (fin/e "x" "y") string?))]
has to cycle through the finite enumerations until they
are exhausted before producing the rest of the natural
numbers:
@enum-example[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                          (cons nat/e number?)
                          (cons (fin/e "x" "y") string?))
              14]
In general, this means that @racket[disj-sum/e] must track the
ranges of natural numbers when each finite enumeration is exhausted
to compute which enumeration to use for a given index.

We provide a fixed-point combinator for
recursive enumerations:
@racket[fix/e : (enum → enum) → enum].
For example, we can construct an enumerator
for lists of numbers:
@racketblock[(fix/e (λ (lon/e)
                      (disj-sum/e (cons (fin/e null)
                                        null?)
                                  (cons (cons/e nat/e lon/e)
                                        cons?))))]
and here are its first @racket[12] elements:
@enum-example[(fix/e (λ (lon/e)
                        (disj-sum/e (cons (fin/e null) null?)
                                    (cons (cons/e nat/e lon/e) cons?))))
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
                             nat/e))]

Also, we can exploit the bijection to define the @racket[except/e]
enumerator. It accepts an element and an enumeration, and returns one
that doesn't have the given element. For example, the first
16 elements of @racket[(except/e nat/e 13)] are
@enum-example[(except/e nat/e 13) 16]
The decoder for @racket[except/e] simply encodes the
given element and then either subtracts one before
passing the natural number along (if it is above the 
given exception) or doesn't (if it isn't). The decoder uses
similar logic.

One important point about the combinators used so far: the
decoding function is linear in the number of bits in the
number it is given. This means, for example, that it takes only
a few milliseconds to compute the
@raw-latex|{\(2^{100,000}\)}|th element
in the list of natural number enumeration given above.

@; xxx put in a \newpage

Our next combinator @racket[dep/e] doesn't always have this property.
It accepts an enumerator and a function from elements to enumerators;
it enumerates pairs of elements where
the enumeration used for the second position in the pair depends
on the actual values of the first position.
For example, we can define an enumeration of ordered pairs 
(where the first position is smaller than the second) like this:
@racketblock[(dep/e nat/e (λ (i) (nats-above/e i)))]
Here are the first 12 elements of the enumeration:
@enum-example[(dep/e nat/e (λ (i) (nats-above/e i)))
              12]
The @racket[dep/e] combinator assumes that if any of the enumerations
produced by the dependent function are infinite then all
of them are. 
The implementation of @racket[dep/e] has three different
cases, depending on the cardinality of the enumerators it
receives. If all of the enumerations are infinite, then it
is just like @racket[cons/e], except
using the dependent function to build the enumerator to select
from for the second element of the pair. Similarly, if the
second enumerations are all infinite but the first one is finite,
then @racket[dep/e] can use quotient and remainder to compute
the indices to supply to the given enumerations when decoding.
In both of these cases, @racket[dep/e] preserves the good
algorithmic properties of the previous combinators, requiring
only linear time in the number of bits of the representation
of the number for decoding.

The troublesome case is when the 
second enumerations are all finite. In that case, we
think of the second component of the pair being drawn from
a single enumeration that consists of all of the
finite enumerations, one after the other. Unfortunately,
in this case, the @racket[dep/e] enumerator must compute
all of the enumerators for the second component as soon
as a single (sufficiently large) number is passed to decode,
which can, in the worst case, take time proportional the
magnitude of the number during decoding.
