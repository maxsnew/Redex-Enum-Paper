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

@title[#:tag "sec:fair-informal"]{Fairness, Informally}

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
but informal way, giving a rationale for our definitions
and some examples to clarify them.

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



It is tempting to think of fairness as simply a notion
of size, perhaps the number of bits required to represent
the result elements of the enumeration. This is not a helpful
perspective, however, because it leaves open the representation
choice and how to count the number of bits required. Indeed,
one could say that the representation of a pair is the binary
representation of the index into some (possibly unfair) enumeration,
thus depriving us of a way to distinguish fair from unfair
enumerations.

Also, we cannot simply restrict 
the combinators to work completely in lock-step on their argument
enumerations, or else we would not admit @emph{any} pairing operation
as fair. After all, a combinator that builds the pair
of @racket[(below/e +inf.0)] with itself must eventually produce the pair
@racket['(1 . 1000)], and that pair must come either before or
after the pair @racket['(1000 . 1)]. So if we insist that, at
every point in the enumeration, the combinator's result enumeration
has used all of its argument enumerations equally, then pairing would
be impossible to do fairly.

Instead, we insist that there are infinitely many places in
the enumeration where the combinators reach an equilibrium.
That is, there are infinitely many points where the result
of the combinator has used all of the argument enumerations
equally.

We also refine fair combinators, saying that a combinator is
@texmath{f}-fair if the @texmath{n}th equilibrium point is at
@texmath{f(n)}. Parameterizing fairness by this function gives us
a way to quantify fair combinators, preferring those that
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

