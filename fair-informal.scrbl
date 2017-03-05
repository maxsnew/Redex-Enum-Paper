#lang scribble/base

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          racket/math
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
    #:contract (list/c natural? natural?
                       natural? natural?)))

This section introduces our definition of fairness in a precise
but informal way, giving a rationale for our definitions
and some examples to clarify them.

A fair enumeration combinator is one that indexes into its
argument enumerations in equal proportions, instead of indexing
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
The upper row of histograms correspond to the fair enumerators and
the lower row corresponds to the unfair enumerators. Each of the four
columns of histograms corresponds to a particular position in the four-tuple.
The @texmath{x}-coordinates of each plot corresponds to the different
values that appear in the tuples and the height of each bar is
the number of times that particular number appears when enumerating
the first @(add-commas unfairness-histograms-total-size) tuples.

For example, the relative height of the leftmost bar in the
two leftmost histograms says that zero appears much less
frequently in the first component of the four tuples when
using the unfair enumerator than using the fair one.
Similarly, the relative height of the leftmost bar in the
two rightmost histograms says that zero appears much more
frequently in the fourth component of the four tuples when using
the unfair enumerator than it does when using the fair one.

More generally, all four components have roughly the
same set of values for the fair tupling operation, but the first tuple
element is considerably different from the other three when using the
unfair combination.

@figure*["fig:unfairness"
         @list{Histograms of the occurrences of each natural number
          in fair and unfair tuples.}
         (parameterize ([plot-width 101 #;135]
                        [plot-height 101 #;135])
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

We can take that basic idea and weaken a little bit, however.
Instead of insisting they use their arguments completely in lock-step,
we insist that there are infinitely many places in the result enumeration
where they have used their input enumerators equally. We call these
special places @emph{equilibrium points}. For example, consider
the @racket[(list/e (below/e +inf.0) (below/e +inf.0))] enumeration;
here are the its first 9 elements:
@enum-example[(list/e (below/e +inf.0) (below/e +inf.0)) 9]
At this point in the enumeration, we have seen all of the numbers
in the interval @texmath{[0,2]} in both elements of the pair and
we have not seen anything outside that interval. That makes
9 an equilibrium point. The 10th element of the enumeration
is @code{@(format "~v" (from-nat (list/e (below/e +inf.0) (below/e +inf.0)) 10))},
and thus 10 is not an equilibrium point because we have seen
the number 3 in one component of the pair, but not in the other
component. In general, @racket[(list/e (below/e +inf.0) (below/e +inf.0))]
has an equilibrium point at every perfect square.
Similarly, here are the first 8 elements of
@racket[(list/e (below/e +inf.0) (below/e +inf.0) (below/e +inf.0)) 8]:
@enum-example[(list/e (below/e +inf.0) (below/e +inf.0) (below/e +inf.0)) 8]
This is an equilibrium point because we have seen 0 and 1
in every component of the pair, but no numbers larger than that.
In general that enumeration has equilibrium points at every perfect cube.

An unfair combinator is one where there are only a finite number of
equilibrium points (or, equivalently, there is a point in the result
enumeration after which there are no more equilibrium points).
As an example consider
@racket[triple/e]:
@racketblock[(define (triple/e e_1 e_2 e_3)
               (list/e e_1 (list/e e_2 e_3)))]
and the first 25 elements of its enumeration:
@enum-example[(list/e (below/e +inf.0) (list/e (below/e +inf.0) (below/e +inf.0))) 24]
The first argument enumeration has been called with
@racket[3] before the other arguments have been called with @racket[2]
and the first argument is called with @racket[4] before the others are
called with @racket[3]. This behavior persists for all input indices,
so that no matter how far we go into the enumeration, there will never
be another equilibrium point after @racket[0].

We also refine fair combinators, saying that a combinator is
@texmath{f}-fair if the @texmath{n}th equilibrium point is at
@texmath{f(n)}. Parameterizing fairness by this function gives us
a way to quantify fair combinators, preferring those that
reach equilibrium more often.
