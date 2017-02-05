#lang scribble/base

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          data/enumerate/lib
          plot
          scriblib/figure
          (only-in scribble/core element style)
          redex/pict
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair-combinators"]{Fair Combinators}

@(element (style "Pairmn" '()) '())

@figure["fig:biased-pair-pict" "Biased Pair Order"]{
  @centered{@biased-cons-pict[]}
}


Once we know that nesting pairs is not going to be fair
in general, how do we define a fair tupling operation?
As we saw in @secref["sec:enum"], the fair pairing operation
traces out two of the edges of ever-increasing squares in the plane.
These ever-increasing squares are at the heart of its fairness.
In particular, the bottom-right-most point in each square is
the equilibrium point, where it has used the two argument
enumerations on exactly the same set of values. 

We can generalize this idea to tracing out the faces of ever-increasing
cubes for three-tuples, and ever-increasing hypercubes in general. 
And at each dimension, there is a ``layering'' property that is preserved.
At the corners of the cubes in three dimensions, we will have traced out
all three faces of each the current cube and all of the smaller cubes
and thus have used all of the argument enumerations the same amount.
And similarly for the corners of the hypercubes in @raw-latex{$n$} dimensions.

So, we need to generalize the pairing function to compute
which face of which hypercube we are on at each point in the
enumeration. Returning to two dimensions, say we want the
44th element of the enumeration. To do so, we first compute the
integer square root, 6, and then compute the remainder (i.e.
44-6@raw-latex{$^2$}), 8. The 6 tells us that we are in the sixth layer,
where all pairs have a 6 and there are no elements larger
than 6. The remainder 8 tells us that we are at the 8th
such pair, which is @racket['(6 . 2)], since we (arbitrarily)
decided to put pairs with a 6 in the second point first.

To perform the inverse, we take @racket['(6 . 2)] and note that
its max is 6. Then we need to determine which position @racket['(6 . 2)]
is in the enumeration of pairs with max of 6. It is 8, and so we
then square the 6 and add 8 to get 44.

This process generalizes to @raw-latex{$n$} dimensions. We take the 
@raw-latex{$n$}th root to find which layer we are in. Then we take
the remainder and use that to index into an enumeration of @raw-latex{$n$}-tuples 
that has at least one @raw-latex{$n$} and whose other values are all
less than or equal to @raw-latex{$n$}. At a high-level, this has reduced the problem
from a @raw-latex{$n$}-dimension problem to an @raw-latex{$n-1$} dimensional
problem, since we can think of the faces of the @raw-latex{$n$} dimensional
hypercube as @raw-latex{$n-1$} dimensional hypercubes. It is not
just a recursive process at this point, however, since the 
@raw-latex{$n-1$} dimensional problem has the additional constraint that
the enumeration always produce @raw-latex{$n-1$} tuples containing
at least one @raw-latex{$n$} and no values larger than @raw-latex{$n$}.

We can, however, produce the enumerations inside the layers
recursively.  In the general case, we need to enumerate sequences of
naturals whose elements have a fixed maximum (i.e. the elements of the
sequence are all less than the maximum and yet the maximum definitely
appears).  This enumeration can be handled with the combinators
discussed in @secref["sec:enum"]. Specifically, an @raw-latex{$n$}
tuple that contains a maximum of @raw-latex{$m$} is either
@raw-latex{$m$} consed onto the front of an @raw-latex{$n-1$} tuple
that has values between 0 and @raw-latex{$m$} or it is a number less
than @raw-latex{$m$} combined with an @raw-latex{$n-1$} tuple that has
a maximum of @raw-latex{$m$}.

The combinatorially-inclined reader may wonder why we do not use the classic Cantor
pairing function.
The two bijections are similar; they are both quadratic
functions with geometric interpretations.
@citet[elegant-pairing-function]'s traces out the
edges of squares and Cantor's traces out the bottoms
of triangles. Importantly, they are both fair (but
with different equilibrium points).

For enumerations we are primarily concerned with the other
direction of the bijection, since that is the one used to generate
terms. In the pairing case, the Cantor function has a fairly
straightforward inverse, but its generalization does not. This is
the generalization of the cantor pairing function to length
@texmath{k} tuples:
@centered{@raw-latex{\vspace*{-.02in}}
           @raw-latex{\textit{cantor\_tuple}$(n_1,n_2,\ldots,n_k) =$}
           @raw-latex{\vspace*{.05in}}
@raw-latex{${{k-1+n_1+\cdots+n_k}\choose{n}}+\cdots+{{1+n_1+n_2}\choose{2}} +
{{n_1}\choose{1}}$}}
We can easily define an inefficient (but correct) way to compute
the inverse by systematically trying every tuple by using a different untupling function, applying the
original @raw-latex{\textit{cantor\_tuple}} function to see if it was the
argument given. @citet[inverting-cantor-n-tupling] gives
the best known algorithm that shrinks the search space considerably, 
but the algorithm there is still a search procedure, and we found it
too slow to use in practice. That said, our library implements 
@citet[inverting-cantor-n-tupling]'s algorithm (via 
a keyword argument to @racket[cons/e] and @racket[list/e]), in
case someone finds it useful.

The @racket[or/e] enumeration's fairness follows a similar, but much
simpler pattern. In particular, the binary @racket[or/e] is fair
because it alternates between its arguments.
As with pairing, extending @racket[or/e] to an @texmath{n}-ary combinator 
via nested calls of the binary combinator is unfair.
Fixing this enumeration is straightforward;
divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use and the quotient
to determine what to index into the enumeration with.
