#lang scribble/base
@(require data/enumerate/lib
          plot/pict
          scribble/manual
          pict
          "enum-util.rkt"
          "util.rkt")

@title{Future Work}

There are two ways in which our definitions of fairness
fails to satisfy: for finite enumerations and for
combinators that build enumerations of recursively specified
data structures.

Consider the enumeration of a finite disjoint sum where
the result enumeration first exhausts the first argument
before considering any of the other arguments. This enumerator
feels like it should be considered unfair and an enumerator
that interleaves the arguments should be considered fair.
Unfortunately, our definition of fairness requires an infinite
number of equilibrium points to make sense and finite enumerations
eventually run out.

@(define listof/e-limit 500)

For recursive data structures, our definition of fairness
requires (at least) binary combinators. That is, our
definition of enumerations of, for example, lists
is not a candidate for fairness because it accepts only
one argument. That said, however, there is more than one way
to define an enumeration of lists that seem to be either fair
or not. For example, the @racket[lon/e] enumeration
from @secref["sec:enum"] tends to bias towards shorter lists
that have bigger numbers at the front of the list in an unfair way.
In contrast, this enumeration:
@lon2/e-code
uses a dependent pair to first select the length of a list
and then to generate an enumeration of lists of that length.
This enumeration balances the length of the list with the elements
of the list in a way that seems more fair. Concretely, here
is a histogram of the lengths of the lists from the first
@(add-commas listof/e-limit) elements of the two enumerations. The
red circles are the lengths of the @racket[lon/e] enumeration and the
blue stars are the lengths of the enumeration that uses the dependent
pair. 

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


@(scale (build-length-stats) .9)

The idea of using dependent pairing to first select a
``shape'' for a the data structure and then to stitch it
together with enumerations for content of the data-structure
is general and can be used to generate trees of arbitrary
shapes. And this approach seems like it should be considered
fair, but we do not yet have a formal characterization of
fairness that captures this difference.
