#lang scribble/sigplan

@(require pict
          scribble/manual
          racket/draw
          data/enumerate/lib
          plot
          scriblib/figure
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title{Union}
@(define either-index 77)
@(define quot (quotient either-index 2))
@(define remainder (modulo either-index 2))
@(define choice/e (if (remainder . = . 0) natural/e string/e))
@(define value  (from-nat choice/e quot))

@;TODO: make the numbers look the same

Our union combinator, @racket[or/e], when viewed as a binary operation
alternates between its 2 arguments. First, it enumerates its arguments
at @racket[0], then @racket[1], etc. To index into @racket[(or/e natural/e string/e)]
at @(add-commas either-index) (where @racket[string/e] is an
enumeration of strings), we just divide by @racket[2] to get
@(add-commas quot) with a remainder of @(add-commas remainder). The
@(add-commas remainder) tells us to index into the @racket[string/e]
enumeration with index @(add-commas quot), giving us @value .

To go the other way, use the contracts on the enumerations to
determine which enumeration a value came from. In which case, we have
a string so we know it came from @racket[string/e]. Then unindex that
value to get its index @(add-commas quot), then multiply that by
@racket[2] and add @racket[1] since it came from @racket[string/e] to
get the original value of @(add-commas either-index).

The typical way to extend to an @texmath{n}-ary combinator would be to
map to nested calls of the binary combinator. Consider a trinary
version implemented this way:

@(define (or-three/e e_1 e_2 e_3)
   (or/e e_1 (or/e e_2 e_3)))
@racketblock[(define (or-three/e e_1 e_2 e_3)
               (or/e e_1 (or/e e_2 e_3)))]

then enumerating some of the first elements of               
@racket[(or-three/e (cons natural/e nat?) (cons symbol/e sym?) (cons float/e float?))]
indicates it is unfairly weighted to the first argument, as shown on the left in @figure-ref["fig:disj-sum"].

@figure["fig:disj-sum" "Unfair (left) and fair (right) disjoint union enumerations"]{
@centered{@(hc-append 60 (disj-sum-pict/bad) (disj-sum-pict/good))}
}

For @racket[k] enumeration arguments, the algorithm is very
similar. Just divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use.

Finally, with finite arguments @racket[or/e] approximates the infinite
behavior until an argument is exhausted:

@racketblock[(or/e (fin/e 'a 'b 'c 'd)
                   natural/e
                   (fin/e "x" "y"))]
@enum-example[(or/e (fin/e 'a 'b 'c 'd)
                   natural/e
                   (fin/e "x" "y"))
              14]

The implemenatation finds the ranges of natural numbers when each
finite enumeration is exhausted to compute which enumeration to use
for some index.

