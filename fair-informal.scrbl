#lang scribble/sigplan

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          data/enumerate/lib
          plot
          scriblib/figure
          redex/pict
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair-informal"]{Fairness and Fair Combinators}

@(define one-billion 1000000000)
@(define fair-number-past-one-billion (* 1000 one-billion))
@(unless (integer? (sqrt (sqrt fair-number-past-one-billion)))
   (error 'ack! "not fair!"))
@(define fair-four-tuple 
   (map/e
    (λ (x) (list (caar x) (cdar x) (cadr x) (cddr x)))
    (λ (l) (cons (cons (list-ref l 0) (list-ref l 1))
                 (cons (list-ref l 2) (list-ref l 3))))
    (cons/e
     (cons/e (below/e +inf.0) (below/e +inf.0))
     (cons/e (below/e +inf.0) (below/e +inf.0)))
    #:contract (list/c exact-nonnegative-integer? exact-nonnegative-integer?
                       exact-nonnegative-integer? exact-nonnegative-integer?)))

This section introduces our definition of fairness in a precise
but informal way and explains why we had to generalize pairing and
alternation in a new way. The subsequent section makes the definitions
formal and gives proofs of various related properties.

A fair enumeration combinator is one that indexes into its
argument enumerations roughly equally, instead of indexing
deeply into one and shallowly into another one. For
example, imagine we wanted to build an enumeration for lists
of length 4. This enumeration is one way to build it:
@racketblock[(cons/e (below/e +inf.0)
              (cons/e (below/e +inf.0) 
               (cons/e (below/e +inf.0)
                (cons/e (below/e +inf.0) 
                 (fin/e null)))))]
The @(add-commas one-billion)th element is
@code{@(format "~v"
               (from-nat (cons/e
                          (below/e +inf.0)
                          (cons/e
                           (below/e +inf.0)
                           (cons/e
                            (below/e +inf.0)
                            (cons/e
                             (below/e +inf.0)
                             (fin/e null)))))
                         one-billion))}
and, as you can see, it has unfairly indexed far more deeply into the first
@racket[(below/e +inf.0)] than the others. In contrast, if we balance the @racket[cons/e]
expressions like this:
@racketblock[(cons/e
              (cons/e (below/e +inf.0) (below/e +inf.0))
              (cons/e (below/e +inf.0) (below/e +inf.0)))]
(and then use @racket[map/e] to adjust the elements of
the enumeration to be lists), then the element at position
@(add-commas one-billion) is
@code{@(format "~v" (from-nat fair-four-tuple one-billion))},
which is much more balanced. This balance is not specific to
just that index in the enumeration, either. @Figure-ref["fig:unfairness"]
shows histograms for each of the components when using
the unfair and the fair four-tuple enumerations. 
The x-coordinates of the plots correspond to the different
values that appear in the tuples and the height of each bar is
the number of times that particular number appears when enumerating
the first @(add-commas unfairness-histograms-total-size) tuples. 
As you can see, all four components have roughly the
same set of values for the fair tupling operation, but the first tuple
element is considerably different from the other three when using the
unfair combination.

@figure*["fig:unfairness"
         @list{Histograms of the occurrences of each natural number
               in fair and unfair tuples}
         (parameterize ([plot-width 135]
                        [plot-height 135])
           (unfairness-histograms))]

The definition of fairness requires some subtlety because we cannot
just restrict 
the combinators to work completely in lock-step on their argument
enumerations, or else we would not admit @emph{any} pairing operation
as fair. After all, a combinator that builds the pair
of @racket[(below/e +inf.0)] with itself we must eventually produce the pair
@racket['(1 . 1000)], and that pair must come either before or
after the pair @racket['(1000 . 1)]. So if we insist that at
every point in the enumeration that the combinator's result enumeration
has used all of its argument enumerations equally, then pairing would
be impossible to do fairly.

Instead, we insist that there are infinitely many places in
the enumeration where the combinators reach an equilibrium. That is,
there are infinitely many points where the result of the combinator
has used all of the argument enumerations equally.

We also refine fair combinators, saying that a combinator is
@texmath{f}-fair if the @texmath{n}th equilibrium point is at
@texmath{f(n)}. Parameterizing fairness by this function gives us
a way to say to quantify fair combinators, preferring those that
reach equilibrium more often.

As an example, consider the fair nested @racket[cons/e]
from the beginning of the section. As we saw, at the point @(add-commas one-billion),
it was not at equilibrium. But at @(add-commas (- fair-number-past-one-billion 1)),
it produces 
@code{@(format "~v" (from-nat fair-four-tuple (- fair-number-past-one-billion 1)))},
and it has indexed into each of the four @racket[below/e] enumerations
with each of the first @(add-commas (sqrt (sqrt fair-number-past-one-billion))) natural numbers.
In general, that fair four-tuple reaches an equilibrium point at every
@texmath{n^4} and @racket[(cons/e (below/e +inf.0) (below/e +inf.0))]
reaches an equilibrium point at every perfect square.

As an example of an unfair combinator consider
@racket[triple/e]:
@racketblock[(define (triple/e e_1 e_2 e_3)
               (cons/e e_1 (cons/e e_2 e_3)))]
and the first 25 elements of its enumeration:
@enum-example[(cons/e (below/e +inf.0) (cons/e (below/e +inf.0) (below/e +inf.0))) 24]
The first argument enumeration has been called with
@racket[3] before the other arguments have been called with @racket[2]
and the first argument is called with @racket[4] before the others are
called with @racket[3]. This behavior persists for all input indices,
so that no matter how far we go into the enumeration, there will never
be an equilibrium point after @racket[0].

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
such pair, which is @racket['(6 . 2)] (since we (arbitrarily)
decided to put pairs with a 6 in the second point first).

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
pairing function, which can be interpreted as a more
triangular grid walk: @centered{@cantor-cons-pict[]}

The two bijections are quite similar; they are both quadratic
functions with similar geometric interpretations.
@citet[elegant-pairing-function]'s traces out the
edges of increasingly large squares and Cantor's traces out the bottoms
of increasingly large triangles. Importantly, they are both fair (although
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
We can easily define a inefficient (but correct) way to compute
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
via nested calls of the binary combinator is unfair. Consider a trinary
version implemented this way:
@(define (or-three/e e_1 e_2 e_3)
   (or/e e_1 (or/e e_2 e_3)))
@racketblock[(define (or-three/e e_1 e_2 e_3)
               (or/e e_1 (or/e e_2 e_3)))]
and consider passing in an enumeration of naturals,
one of symbols, and one of floats.
The left side of @figure-ref["fig:disj-sum"] shows the order used by
the unfair nesting and the right side shows the fair ordering.

@figure["fig:disj-sum" "Unfair (left) and fair (right) disjoint union enumerations"]{
@centered{@(hc-append 60 (disj-sum-pict/bad) (disj-sum-pict/good))}
}

Fixing this enumeration is straightforward;
divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use and the quotient
to determine what to index into the enumeration with.
