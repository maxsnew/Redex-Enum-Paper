#lang scribble/lncs

@(require scribble/manual
          scribble/eval
          racket/list
          redex/private/enumerator
          scribble/core
          "util.rkt"
          "enum-util.rkt")

@;{

- implementation points:
   => representation as three-tuples (size, two functions forming a bijection)
   => running time as linear in the bit representation
   
}

@title[#:tag "sec:enum"]{Enumeration Combinators}

Our enumeration library provides some basic enumerations and combinators
to build up more complex ones and this section gives an overview
of the combinators. Each enumerator consist of three pieces:
a @racket[to-nat] function that computes the index of anything in the enumeration,
a @racket[from-nat] function that computes a value from an index, and a size
of the enumeration, which can be either a natural number or @racket[+inf.0]. In addition,
the @racket[to-nat] and @racket[from-nat] functions form a bijection between
the natural numbers (up to the size) and the values that are being enumerated.

The most basic enumerator is @racket[nats/e]. Its @racket[to-nat]
and @racket[from-nat] functions are simply the identity function
and its size is @racket[+inf.0]. The combinator @racket[fin/e]
builds a finite enumeration 
from its arguments, so @racket[(fin/e 1 2 3 "a" "b" "c")] is
an enumeration with the six given elements, where the elements
are put in correspondence with the naturals in order they are
given.

The next combinator is the pairing operator 
@racket[cons/e]. It takes two enumerations and returns an
enumeration of pairs of those values. If one of the
enumerations is finite, the enumeration loops through the
finite enumeration, pairing each with an element from the
other enumeration. If both are finite, we loop through the
one with lesser cardinality. This corresponds to taking the
quotient with remainder of the index with the lesser size.

Pairing infinite enumerations require more care. If we
imagine our sets as being laid out in an infinite two dimensional table,
@racket[cons/e] walks along the edge of ever-widening
squares to enumerate all pairs:
@centered{@pair-pict[]}
which means that @racket[(cons/e nat/e nat/e)]'s
first @racket[15] elements are
@enum-example[(cons/e nat/e nat/e) 15]

The n-ary @racket[list/e] generalizes the binary @racket[cons/e]
that can be interpreted as a similar walk in an
n-dimensional grid. We discuss this in detail in @secref["sec:fair"].

The disjoint union enumerator, @racket[disj-sum/e], takes two or more
pairs of enumerators and predicates. The predicates
must distinguish the elements of the enumerations from
each other. The
resulting enumeration alternates between the input
enumerations, so that if given @racket[n] infinite
enumerations, the resulting enumeration will alternate
through each of the enumerations every @racket[n] positions.
For example, the following is the beginning of the disjoint
sum of an enumeration of natural numbers and an enumeration
of strings
@enum-example[(disj-sum/e (cons nat/e number?)
                          (cons string/e string?))
              18]
We generalize this combinator and describe it in detail in
@secref["sec:fair"] as well.
              
The combinator
@racket[fix/e : (enum → enum) → enum] computes
takes fixed points of enumerator functionals in
order to build recursive enumerations.
For example, we can construct an enumerator
for lists of numbers:
@racketblock[
(fix/e (λ (lon/e)
         (disj-sum/e (cons (fin/e null) null?)
                     (cons (cons/e nat/e lon/e) cons?))))]
and here are its first @racket[15] elements:
@enum-example[(fix/e (λ (lon/e)
                       (disj-sum/e (cons (fin/e null) null?)
                                   (cons (cons/e nat/e lon/e) cons?))))
               15]
A call like @racket[(fix/e f)] enumerator 
calls @racket[(f (fix/e f))] to build the enumerator,
but it waits until the first time encoding or decoding 
happens before computing it. This means that a use of
@racket[fix/e] that is too eager, e.g.:
@racket[(fix/e (λ (x) x))] will cause its @racket[from-nat]
function to fail to terminate.
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
sets with the bijection in an enumeration, so we can, for example, construct 
enumerations of natural numbers that start at some point beyond zero:
@racketblock/define[(define (nats-above/e i)
                      (map/e (λ (x) (+ x i))
                             (λ (x) (- x i))
                             nat/e))]

Also, we can exploit the bidirectionality of our enumerators to define
the @racket[except/e] enumerator. It accepts an element and an
enumeration, and returns one that doesn't have the given element. For
example, the first 22 elements of @racket[(except/e nat/e 13)] are
@enum-example[(except/e nat/e 13) 22] The @racket[from-nat] function
for @racket[except/e] simply uses the original enumerator's
@racket[to-nat] on the given element and then either subtracts one
before passing the natural number along (if it is above the given
exception) or simply passes it along (if it is below). Similarly, the
@racket[except/e]'s @racket[to-nat] function calls the input
enumerator's @racket[to-nat] function.

One important point about the combinators used so far: the
decoding function is linear in the number of bits in the
number it is given. This means, for example, that it takes only
a few milliseconds to compute the
@raw-latex{$2^{100,000}$}th element
in the list of natural number enumeration given above.

Our next combinator @racket[dep/e] does not always have this property.
It accepts an enumerator and a function from elements to enumerators;
it enumerates pairs of elements where
the enumeration used for the second position in the pair depends
on the actual values of the first position.
For example, we can define an enumeration of ordered pairs 
(where the first position is smaller than the second) like this:
@racketblock[(dep/e nat/e (λ (i) (nats-above/e i)))]
Here are the first 15 elements of the enumeration:
@enum-example[(dep/e nat/e (λ (i) (nats-above/e i)))
              15]
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
