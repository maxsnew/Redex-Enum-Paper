#lang scribble/base
@(require data/enumerate/lib
          plot/pict
          scribble/manual
          pict
          "enum-util.rkt"
          "util.rkt")

@title{Future Work}

There are two ways in which we we believe more work with our
definitions and use of fairness would be productive.

@section{Enumerations of Recursive Structures}

@(define listof/e-limit 500)
@(define lon/e-example (expt 10 10))

Our definition of fairness requires (at least) binary
combinators. That is, a definition of enumerations of, for
example, lists is not a candidate for our fairness
definition because it accepts only one argument (the
enumeration of the elements). There is, however, more than
one way to define an enumeration of lists and some ways seem
to more fair than others. More precisely, the @racket[lon/e]
enumeration from @secref["sec:enum"] tends to bias towards
shorter lists that have bigger numbers at the front of the
list in an unfair way. For example, the
@add-commas[lon/e-example]th element is
@(code (format "~v" (from-nat lon/e lon/e-example))),
which seems to suggest that @racket[lon/e] is exploring the
first element at the expense of exploring longer lists.

Instead, we can build an enumeration that first selects a
length of the list and then uses a dependent enumeration to
build a fair @texmath{n}-tuple of the corresponding length, i.e.:
@lon2/e-code
This enumeration balances the length of the list with the
elements of the list in a way that, at least intuitively, seems more fair.
Concretely, here is a histogram of the lengths of the lists
from the first
@(add-commas listof/e-limit) elements of the two
enumerations. The red circles are the lengths of the 
@racket[lon/e] enumeration and the blue stars are the
lengths of the enumeration above that uses the dependent pair. 

@(define (build-length-stats)
   (define (get-points e color sym)
     (define lengths (make-hash))
     (for ([x (in-range listof/e-limit)])
       (define lst (from-nat e x))
       (define len (length lst))
       (hash-set! lengths len (+ 1 (hash-ref lengths len 0))))
     (values (points
              #:sym sym
              #:color color
              (for/list ([(k v) (in-hash lengths)])
                (vector k v)))
             (car (sort (hash-keys lengths) >))
             (car (sort (hash-values lengths) >))))
   (define-values (lon-points lon-x-max lon-y-max) (get-points lon/e "red" 'circle))
   (define-values (lon2-points lon2-x-max lon2-y-max) (get-points lon2/e "blue" '5star))
   (plot-pict
    #:width 300
    #:height 200
    #:x-label "Length"
    #:y-label "Number of lists at that length"
    #:x-min -1
    #:x-max (+ 1 (max lon-x-max lon2-x-max))
    #:y-min -10
    #:y-max (+ 10 (max lon-y-max lon2-y-max))
    (list lon-points lon2-points)))

@centered{@(build-length-stats)}

The idea of using dependent pairing to first select a
``shape'' for the data structure and then to stitch it
together with enumerations for content of the data-structure
is general and can be used to generate trees of arbitrary
shapes. And this approach seems like it should be considered
fair, but we do not yet have a formal characterization of
fairness that captures the difference between the two approaches
to defining data-structure enumerators. 

We hope that someday someone is able to capture this notion
but there is one other wrinkle worth mentioning: the
seemingly fair enumeration is much slower. Enough
that the built-in list combinator in our enumeration library
does not provide that enumeration strategy by default
(although it is an option that is easy to use).

@section{Intentional Unfairness}

The second way in which our notion of fairness is incomplete has to
do with real-world testing. Consider, for example, this definition
of a grammar for the lambda calculus (written in Redex's notation):
@racketblock[(define-language L
               (e ::=
                  x
                  (e e)
                  (λ (x) e))
               (x ::= variable))]

Our implementation translates the @racket[e] non-terminal
into uses of the @racket[or/e] enumeration combinator for
the productions and the @racket[list/e] combinator for
each production to combine the pieces, as you might expect.
Looking at a prefix of the enumeration, however, clearly
suggests that it is not-optimal for most bug-finding tasks.
In particular, every third expression generated is simply just a
free variable!

We think that, while fairness is a good guide for combinators, it is
important to be able to selectively bias the enumerations away from
fairness (much like the bias used to obtain fairness, as discussed in
@secref["sec:fair-combinators"]).

We have not explored how to specify these biases in Redex nor their
impact on testing, but believe that a domain-specific language
for tuning the enumerations is worthy of more study.