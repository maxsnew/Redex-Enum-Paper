#lang scribble/base
@(require data/enumerate/lib
          plot/pict
          scribble/manual
          pict
          "enum-util.rkt"
          "util.rkt")

@title{Future Work}

We are unsatisfied with one aspect of our definition of
fairness, namely that it does not capture what intuitively
seems to be unfair behavior in enumerations of recursively
specified data structures.

@(define listof/e-limit 500)

Our definition of fairness requires (at least) binary
combinators. That is, our definition of enumerations of, for
example, lists is not a candidate for our fairness definition because it
accepts only one argument. There is, however, more
than one way to define an enumeration of lists that seem to
be either fair or not. For example, the @racket[lon/e]
enumeration from @secref["sec:enum"] tends to bias towards
shorter lists that have bigger numbers at the front of the
list in an unfair way. Instead, consider an enumeration that
first selects a length of the list and then uses a dependent
enumeration to build a fair n-tuple of the corresponding
length, like this code does:
@lon2/e-code
This enumeration balances the length of the list with the
elements of the list in a way that seems more fair.
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

@centered{@(scale (build-length-stats) .9)}

The idea of using dependent pairing to first select a
``shape'' for the data structure and then to stitch it
together with enumerations for content of the data-structure
is general and can be used to generate trees of arbitrary
shapes. And this approach seems like it should be considered
fair, but we do not yet have a formal characterization of
fairness that captures this difference.

We hope that someday someone is able to capture this notion
but there is one other wrinkle worth mentioning: the
seemingly fair enumeration is much slower. Enough
that the built-in list combinator in our enumeration library
does not provide that enumeration strategy by default
(although it is an option that is easy to use).
