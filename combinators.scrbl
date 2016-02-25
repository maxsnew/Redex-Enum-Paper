#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          scriblib/figure
          racket/list
          racket/contract
          data/enumerate/lib
          scriblib/footnote
          scribble/core
          "util.rkt"
          "enum-util.rkt"
          "cite.rkt")

@title[#:tag "sec:enum"]{Introduction to Enumeration}

This section introduces the basics of enumeration
via a tour of our Racket-based enumeration library.
Each enumeration in our library consists of four pieces:
a @racket[to-nat] function that computes the index of any value in the enumeration,
a @racket[from-nat] function that computes a value from an index, the size
of the enumeration, which can be either a natural number or positive infinity 
(written @racket[+inf.0]),
and a contract that captures exactly the values in the enumeration. For the
purposes of this paper, it is sufficient to think of the contracts
as predicates on values; they are more general, but that generality
is not needed to understand the our enumeration library.

Each enumeration has the invariant that
the @racket[to-nat] and @racket[from-nat] functions form a bijection between
the natural numbers (up to the size) and the values that satisfy
the contract.@note{Our library also supports one-way enumerations as
                 they can be useful in practice, but we do not talk
                 about them here.}

The most basic enumeration is @racket[below/e] (by convention, the names of
our enumeration library functions end with @racket[/e]; the slash is a legal character
for an identifier in Racket). The @racket[below/e] combinator accepts a
natural number or @racket[+inf.0] and returns an enumeration
of that size. Its @racket[to-nat] and @racket[from-nat]
functions are simply the identity function. 

@figure["fig:pair-pict" "Pairing Order"]{
  @centered{@pair-pict[]}
}

The disjoint union enumeration, @racket[or/e], takes two or more
enumerations. The resulting enumeration alternates between the input
enumerations, so that if given @racket[n] infinite enumerations, the
resulting enumeration will alternate through each of the enumerations
every @racket[n] positions.  For example, the following is the
beginning of the disjoint union of an enumeration of natural numbers
and an enumeration of strings:

@enum-example[(or/e (below/e +inf.0) string/e)
              7]

The @racket[or/e] enumeration insists that contracts for its arguments
be disjoint so that it can compute the reverse direction of the bijection.
Specifically, given a value, it tests the value to see which argument
enumeration it comes from, and then it finds the position in that enumeration
in order to find the position in the union enumeration.

The next combinator is the pairing operator 
@racket[cons/e]. It takes two enumerations and returns an
enumeration of pairs of those values. If one of the
input enumerations is finite, the result enumeration loops through the
finite enumeration, pairing each with an element from the
infinite enumeration. If both are finite, it loops through the
one with lesser cardinality. This corresponds to taking the
quotient and remainder of the index with the lesser size.

Pairing infinite enumerations requires more care. If we
imagine our sets as being laid out in an infinite two dimensional table,
@racket[cons/e] walks along the edge of ever-widening
squares to enumerate all pairs (using @citet[elegant-pairing-function]'s
bijection), as shown in @figure-ref["fig:pair-pict"].
The n-ary @racket[list/e] generalizes the binary @racket[cons/e]
that can be interpreted as a similar walk in an
@texmath{n}-dimensional grid.
We discuss this in detail in @secref["sec:fair-informal"].

The combinator
@racket[delay/e] facilitates fixed points of enumerations,
in order to build recursive enumerations.
For example, we can construct an enumeration
for lists of numbers:
@lon/e-code
This code says that the @racket[lon/e] enumeration is a disjoint
union of the singleton enumeration @racket[(fin/e null)] (an enumeration
that contains only @racket[null], the empty list) and an enumeration of
pairs, where the first component of the pair is a natural number
and the second component of the pair is again @racket[lon/e]. The
@racket[delay/e] around the latter @racket[lon/e] is what makes the
fixed point work. It simply delays the construction of the enumeration
until the first time something is indexed from the enumeration.
This means that a use of
@racket[delay/e] that is too eager, e.g.:
@racket[(define e (delay/e e))] will cause @racket[from-nat]
to fail to terminate.
Indeed, switching the order of the arguments to @racket[or/e]
above also produces an enumeration
that fails to terminate. Here are the first 12 elements of the correct @racket[lon/e]:
@enum-example[lon/e 12]

Our combinators rely on knowing the
sizes of their arguments as they are constructed, but in a recursive enumeration
this is begging the question. Since it is not possible to
statically know whether a recursive enumeration uses its
parameter, we leave it to the caller to determine the
correct size, defaulting to infinite if not specified.

To build up more complex enumerations, it is useful to be able to 
adjust the elements of an existing enumeration. We use @racket[map/e] 
which composes a bijection between elements of the contract of
a given enumeration and a new contract. Using this we can, for example, construct 
enumerations of natural numbers that start at some natural @racket[i] beyond zero
by using this function @racket[naturals-above/e], that accepts
a natural @racket[i] and returns an enumeration.
@racketblock/define[(define (naturals-above/e i)
                      (map/e (λ (x) (+ x i))
                             (λ (x) (- x i))
                             (below/e +inf.0)
                             #:contract (and/c exact-integer? (>=/c i))))]
The first two arguments to @racket[map/e] are functions that
form a bijection between the values in the enumeration argument
and the contract given as the final argument (@racket[#:contract]
is a keyword argument specifier in this case saying that
the contract is integers larger than or equal to @racket[i]).
As it is easy to make simple mistakes
when building the bijection, @racket[map/e]'s contract randomly checks
a few values of the enumeration to make sure they map back to themselves
when passed through the two functions.

We exploit the bidirectionality of our enumerations to define
the @racket[except/e] enumeration. It accepts an element and an
enumeration, and returns an enumeration without the given element. For
example, the first 9 elements of @racket[(except/e (below/e +inf.0) 4)] are
@enum-example[(except/e (below/e +inf.0) 4) 9] 
The @racket[from-nat] function for @racket[except/e] simply
uses the original enumeration's @racket[to-nat] on the given
element and then either subtracts one (if it is above the given exception) or
simply passes it along (if it is below). Similarly, the 
@racket[except/e]'s @racket[to-nat] function calls the input
enumeration's @racket[from-nat] function.

One important point about the combinators used so far: the
conversion from a natural to a value takes time that is (a low-order)
polynomial in the number of bits in the
number it is given. This means, for example, that it takes only
a few milliseconds to compute the
@raw-latex{$2^{100,000}$}th element
in the list of natural numbers enumeration given above.

Our next combinator, @racket[cons/de], does not always have this property.
It builds enumerations of pairs, but where the enumeration on one
side of the pair depends on the element in the other side of the pair.
For example, we can define an enumeration of ordered pairs 
(where the first position is smaller than the second) like this:
@racketblock[(cons/de [hd (below/e +inf.0)]
                      [tl (hd) (naturals-above/e hd)])]
It is important to note that @racket[cons/de] is not a function (like the earlier
combinators). It is a special expression form with two sub-expressions (in this example:
@racket[(below/e +inf.0)] and @racket[(naturals-above/e i)]),
each of which is named (@racket[hd] and @racket[tl] here).
And one of the expressions may refer to the other's variable by putting it
into parentheses (in this case, the @racket[tl] expression can refer to @racket[hd]).
Here are the first 12 elements of the enumeration:
@enum-example[(cons/de [hd (below/e +inf.0)] 
                       [tl (hd) (naturals-above/e hd)])
              12]
The implementation of @racket[cons/de] has three different
cases, depending on the cardinality of the enumerations it
receives. If all of the enumerations are infinite, then it
is just like @racket[cons/e], except
using the dependent function to build the enumeration to select
from for the second element of the pair. Similarly, if the
independent enumeration is finite and the dependent ones are all
infinite, then @racket[cons/de] can use quotient and remainder to compute
the indices to supply to the given enumerations when decoding.
In both of these cases, @racket[cons/de] preserves the good
algorithmic properties of the previous combinators.

The troublesome case is when the dependent enumerations are
all finite. In that case, we think of the dependent
component of the pair being drawn from a single enumeration
that consists of all of the finite enumerations, one after
the other. Unfortunately, in this case, calling
@racket[from-nat] on the result of @racket[cons/de] can take
time proportional to the magnitude of the input index (or possibly even worse if
computing the dependent enumerations themselves are
costly). We use memoization to avoid repeatedly paying this cost,
but even with memoization this case for @racket[cons/de] is
observably worse in practice.

Our library has a number of other combinators not discussed here, but
these are the most important ones and give a flavor of the capabilities
of enumerations in the library. The documentation (from the link in an earlier
footnote) lists all of the combinators.
