#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          racket/list
          racket/contract
          data/enumerate/lib
          scriblib/footnote
          scribble/core
          "util.rkt"
          "enum-util.rkt"
          "cite.rkt")

@;{

- implementation points:
   => representation as three-tuples (size, two functions forming a bijection)
   => running time as linear in the bit representation
   
}

@title[#:tag "sec:enum"]{Introduction to Enumeration}

This section gives a tour of our enumeration library and
introduces the basics of enumeration. The next section explains
fairness and the rest of the paper discusses our evaluation, related 
work, and concludes.

Our library provides basic enumerations and combinators
that build up more complex ones. Each enumeration consists of four pieces:
a @racket[to-nat] function that computes the index of any value in the enumeration,
a @racket[from-nat] function that computes a value from an index, the size
of the enumeration, which can be either a natural number or positive infinity (written @racket[+inf.0]),
and a contract that captures all of the values in the enumeration precisely.
Each enumeration has the invariant that
the @racket[to-nat] and @racket[from-nat] functions form a bijection between
the natural numbers (up to the size) and the values that are being 
enumerated.@note{Our library also supports one-way enumerations as
                 they can be useful in practice, but we do not talk
                 about them here.}

The most basic enumeration is @racket[natural/e]. Its @racket[to-nat]
and @racket[from-nat] functions are simply the identity function
and its size is @racket[+inf.0]. The combinator @racket[fin/e]
builds a finite enumeration 
from its arguments, so @racket[(fin/e 1 2 3 "a" "b" "c")] is
an enumeration with the six given elements, where the elements
are put in correspondence with the naturals in order they are
given.

The disjoint union enumeration, @racket[or/e], takes two or more
enumerations. The resulting enumeration alternates between the input
enumerations, so that if given @racket[n] infinite enumerations, the
resulting enumeration will alternate through each of the enumerations
every @racket[n] positions.  For example, the following is the
beginning of the disjoint union of an enumeration of natural numbers
and an enumeration of strings:

@enum-example[(or/e natural/e string/e)
              14]

The contracts associated with the enumerations are used to determine
which enumeration a value came from.

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
squares to enumerate all pairs (using @citet[elegant-pairing-function]'s
bijection):
@centered{@pair-pict[]}
which means that @racket[(cons/e natural/e natural/e)]'s
first 12 elements are
@enum-example[(cons/e natural/e natural/e) 12]

The n-ary @racket[list/e] generalizes the binary @racket[cons/e]
that can be interpreted as a similar walk in an
n-dimensional grid.
We discuss this in detail in @secref["sec:fair-informal"].

The combinator
@racket[delay/e] facilitates fixed points of enumerations,
in order to build recursive enumerations.
For example, we can construct an enumeration
for lists of numbers:
@racketblock[
(letrec ([lon/e
          (or/e (fin/e null)
                (cons/e natural/e (delay/e lon/e)))])
  lon/e)]
and here are its first 12 elements:
@enum-example[(letrec ([lon/e
                        (or/e (fin/e null)
                              (cons/e natural/e (delay/e lon/e)))])
                lon/e)
               12]
An expression like @racket[(delay/e lon/e)] returns
immediately, without evaluating the argument to @racket[delay/e].
The first time encoding or decoding 
happens, the value of the expression is computed (and cached). 
This means that a use of
@racket[fix/e] that is too eager, e.g.:
@racket[(letrec ([e (fix/e e)]) e)] will cause @racket[from-nat]
to fail to terminate.
Indeed, switching the order of the arguments to @racket[or/e]
in the above example also produces an enumeration
that fails to terminate when decoding or encoding happens.

Our combinators rely on knowing the
sizes of their arguments as they are constructed, but in a recursive enumeration
this is begging the question. Since it is not possible to
statically know whether a recursive enumeration uses its
parameter, we leave it to the caller to determine the
correct size, defaulting to infinite if not specified.

To build up more complex enumerations, it is useful to be able to 
adjust the elements of an existing enumeration. We use @racket[map/e] 
which composes a bijection between any two
sets with the bijection in an enumeration, so we can, for example, construct 
enumerations of natural numbers that start at some natural @racket[i] beyond zero:
@racketblock/define[(define (naturals-above/e i)
                      (map/e (λ (x) (+ x i))
                             (λ (x) (- x i))
                             natural/e
                             #:contract (and/c exact-integer? (>=/c i))))]
The first two arguments to @racket[map/e] are functions that
form a bijection between the values in the enumeration argument
and the contract given as the final argument (the @racket[#:contract]
is a keyword argument specifier). As it is easy to make simple mistakes
when building the bijection, @racket[map/e]'s contract randomly checks
a few values of the enumeration to make sure they map back to themselves
when passed through the two functions.

We exploit the bidirectionality of our enumerations to define
the @racket[except/e] enumeration. It accepts an element and an
enumeration, and returns an enumeration that doesn't have the given element. For
example, the first 8 elements of @racket[(except/e natural/e 4)] are
@enum-example[(except/e natural/e 4) 8] 
The @racket[from-nat] function for @racket[except/e] simply
uses the original enumeration's @racket[to-nat] on the given
element and then either subtracts one before passing the
natural number along (if it is above the given exception) or
simply passes it along (if it is below). Similarly, the 
@racket[except/e]'s @racket[to-nat] function calls the input
enumeration's @racket[to-nat] function.

One important point about the combinators used so far: the
decoding function is linear in the number of bits in the
number it is given. This means, for example, that it takes only
a few milliseconds to compute the
@raw-latex{$2^{100,000}$}th element
in the list of natural number enumeration given above, for example.

Our next combinator, @racket[cons/de], does not always have this property.
It builds enumerations of pairs, but where the enumeration on one
side of the pair depends on the element in the other side of the pair.
For example, we can define an enumeration of ordered pairs 
(where the first position is smaller than the second) like this:
@racketblock[(cons/de [hd natural/e] [tl (hd) (naturals-above/e hd)])]
A @racket[cons/de] has two subexpressions (@racket[natural/e] and @racket[(naturals-above/e i)]
in this example), each of which is named (@racket[hd] and @racket[tl] in this example).
And one of the expressions may refer to the other's variable by putting it
into parentheses (in this case, the @racket[tl] expression can refer to @racket[hd]).
Here are the first 12 elements of the enumeration:
@enum-example[(cons/de [hd natural/e] 
                       [tl (hd) (naturals-above/e hd)])
              12]
The implementation of @racket[dep/e] has three different
cases, depending on the cardinality of the enumerations it
receives. If all of the enumerations are infinite, then it
is just like @racket[cons/e], except
using the dependent function to build the enumeration to select
from for the second element of the pair. Similarly, if the
independent enumeration is finite and the dependent ones are all
infinite, then @racket[cons/de] can use quotient and remainder to compute
the indices to supply to the given enumerations when decoding.
In both of these cases, @racket[cons/de] preserves the good
algorithmic properties of the previous combinators, requiring
only linear time in the number of bits of the representation
of the number for decoding.

The troublesome case is when the dependent
enumerations are all finite. In that case, we
think of the dependent component of the pair being drawn from
a single enumeration that consists of all of the
finite enumerations, one after the other. Unfortunately,
in this case, the @racket[cons/de] enumeration must compute
all of the enumerations for the second component as soon
as a single (sufficiently large) number is passed to decode,
which can, in the worst case, take time proportional to the
magnitude of the number during decoding.
