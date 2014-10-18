#lang scribble/lncs

@(require pict
          scribble/manual
          racket/draw
          racket/list
          redex/private/enumerator
          plot
          scriblib/figure
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair"]{Fairness}

@(define one-billion 1000000000)
@(define fair-number-past-one-billion (* 1000 one-billion))
@(unless (integer? (sqrt (sqrt fair-number-past-one-billion)))
   (error 'ack! "not fair!"))
@(define fair-four-tuple 
   (map/e
    (λ (x) (list (caar x) (cadr x) (cdar x) (cddr x)))
    (λ (l) (cons (cons (list-ref l 0) (list-ref l 1))
                 (cons (list-ref l 4) (list-ref l 3))))
    (cons/e
     (cons/e nat/e nat/e)
     (cons/e nat/e nat/e))))

A fair enumeration combinator is one that indexes into its
given enumerators roughly equally, instead of indexing
deeply into one and shallowly into a different one. For
example, imagine we waned to build an enumerator for lists
of length 4. This enumerator is one way to build it:
@racketblock[(cons/e nat/e (cons/e nat/e 
              (cons/e nat/e (cons/e nat/e 
               (fin/e null)))))]
Unfortunately, it is not fair. The @(add-commas one-billion)th element is
@code{@(format "~v"
             (decode (cons/e
                      nat/e
                      (cons/e
                       nat/e
                       (cons/e
                        nat/e
                        (cons/e
                         nat/e
                         (fin/e null)))))
                     one-billion))}
and, as you can see, it has indexed far more deeply into the first
@racket[nat/e] than the others. In contrast, if we balance the @racket[cons/e]
expressions like this:
@racketblock[(cons/e
              (cons/e nat/e nat/e)
              (cons/e nat/e nat/e))]
(and then were to use @racket[map/e] to adjust the elements of
the enumeration to actually be lists), then the
@(add-commas one-billion) element is
@code{@(format "~v" (decode fair-four-tuple one-billion))},
which is much more balanced. This balance is not specific to
just that index in the enumeration, either. @Figure-ref["fig:unfairness"]
shows histograms for each of the components when using
the unfair @racket[(cons/e nat/e (cons/e nat/e nat/e))]
and when using a fair tupling that combines three @racket[nat/e] 
enumerators. The x-coordinates of the plot correspond to the different
values that appear in the tuples and the height of each bar is
the number of times that particular number appeared when enumerating
the first 1,000 tuples. As you can see, all three components have the
same set of values for the fair tupling operation, but the first tuple
element is considerably different from the other two when using the
unfair combination.

@figure*["fig:unfairness"
         @list{Histograms of the occurrences of each natural number
               in fair and unfair tuples}
         (parameterize ([plot-width 135]
                        [plot-height 135])
           (unfairness-histograms))]

The subtle point about fairness is that we cannot restrict 
the combinators to work completely in lock-step on their argument
enumerations, or else we would not admit @emph{any} pairing operation
as fair. After all, a combinator that builds the pair
of @racket[nat/e] with itself we must eventually produce the pair
@racket['(1 . 4)], and that pair must come either before or
after the pair @racket['(4 . 1)]. So if we insist that at
every point in the enumeration that the combinator's result enumeration
has used all of its argument enumerations equally, then pairing would
be impossible, as would many other combinators.

Instead, we insist that there are infinitely many places in
the enumeration where the combinators reach an equilibrium. That is,
there are infinitely many points where the result of the combinator
has used all of the argument enumerations equally.

As an example, consider the fair nested @racket[cons/e]
from the beginning of the section. As we saw, at the point @(add-commas one-billion),
it was not at equilibrium. But at @(add-commas (- fair-number-past-one-billion 1)),
it produces 
@code{@(format "~v" (decode fair-four-tuple (- fair-number-past-one-billion 1)))},
and indeed it has indexed into each of the four @racket[nat/e] enumerations
with each of the first @(add-commas (sqrt (sqrt fair-number-past-one-billion))) natural numbers.

In general, that fair four-tuple reaches an equilibrium point at every
@texmath{n^4} and @racket[(cons/e nat/e nat/e)]
reaches an equilibrium point at every perfect square. The
diagonal in the square diagram from @secref["sec:enum"] illustrates
the first few equilibrium points for @racket[(cons nat/e nat/e)].

As an example of an unfair combinator consider
@racket[triple/e]:
@racketblock[(define (triple/e e_1 e_2 e_3)
               (cons/e e_1 (cons/e e_2 e_3)))]
and the first 25 elements of its enumeration:
@enum-example[(cons/e nat/e (cons/e nat/e nat/e)) 24]
The first argument enumeration has been called with
@racket[3] before the other arguments have been called with @racket[2]
and the first argument is called with @racket[4] before the others are
called with @racket[3] this behavior persists for all input indices,
so that no matter how far we go into the enumeration, there will never
be an equilibrium point after @racket['(0 0 . 0)].

Fair combinators give us predictability for programs that
use our enumerators. In Redex, our main application of
enumeration combinators, fairness ensures that when a Redex
programmer makes an innocuous change to the grammar of
the language (e.g. changing the relative order of two
subexpressions in an expression form) the enumeration
quality is not significantly affected. For example, consider
an application expression. From the perspective of the
enumerator, an application expression looks just like a list
of expressions. An unfair enumerator might cause our
bug-finding search to spend a lot of time generating
different argument expressions and always using similar
(simple, boring) function expressions. 

Of course, the flip-side of this coin is that using unfair
combinators can improve the quality of the search in
some cases, even over fair enumeration. For example, when we
are enumerating expressions that consist of a choice between
variables and other kinds of expressions, we do not want to
spend lots of time trying out different variables because most
models are sensitive only to when variables differ from 
each other, not their exact spelling. Accordingly unfairly
biasing our enumerators away from different variables 
can be win for finding bugs. Overall, however, it is important
that we do have a fair set of combinators that correspond
to the way that Redex programs are constructed and then when
Redex programs are compiled into the combinators, the compilation
can use domain knowledge about Redex patterns to selectively
choose targeted unfairness, but still use fair combinators when it
has no special knowledge.

@section{Formal Definition of Fairness}

Our definition of fairness necessitates indexing enumerations with 
arbitrarily large natural numbers, so we restrict our attention
to infinite enumerators.

A function
@texmath{c : Enum(a_1) \cdots Enum(a_k) \to Enum(T(a_1,\cdots,a_k))},
for some type-level function @texmath{T},
is an enumeration combinator if we can extract two functions that fully 
define its bijection. The first,
@texmath{args_c : \mathbb{N} \to ([\mathbb{N}],\ldots,[\mathbb{N}])}
where the output tuple has length @texmath{k}, returns the
@texmath{k}-tuple of lists of indices needed to index into the input
enumerations when decoding from a given index. The second,
@texmath{build_c : ([a_1],\ldots,[a_k]) \to T(a_1,\ldots,a_k)} is a
function that is linear in its input arguments, and thus using all of
its inputs to construct its output. This function
builds a value of the enumeration from components from the argument
enumerations. These functions together fully specify the combinator;
each of the elements of the lists of @texmath{args_c}'s result are 
supplied to the corresponding argument combinator and those results
are then passed to @texmath{build_c}. If one of the lists has no
elements, the corresponding argument combinator is not used and if
one of the lists has multiple elements, the corresponding combinator
is used multiple times.

For convenience, we say that two lists are equivalent if one is a
permutation of the other.

We say that an enumeration combinator @racket[c] is fair if, for every
natural number @raw-latex{$m$}, there exists a natural number
@raw-latex{$M > m$} such that for every @texmath{h,j\in \{1,\ldots,k\}},
if you apply @raw-latex{$args_c$} to every value greater than or equal to
@texmath{0} and less than @texmath{M}, and concatenate all of the
lists in the @texmath{h}th column into a list @texmath{L_h} and in the
@texmath{j}th column into a list @texmath{L_j} then @texmath{L_j}
and @texmath{L_h} are equivalent. In other words, @texmath{M} is an
equilibrium point and thus when enumerating
all values up to @raw-latex{$M$} in the result enumeration, the
values supplied to argument enumerations will all be the same.
Any other combinator is unfair.

@include-section["fair-tuple.scrbl"]

@include-section["fair-union.scrbl"]
