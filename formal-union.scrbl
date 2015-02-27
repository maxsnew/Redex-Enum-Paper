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

@title{Fair Union}

Unsurprisingly, the @racket[or/e] combinator is fair.
@theorem{@racket[or/e] is fair.}
@proof{
We prove that @texmath{2*n} is an equilibrium point for all
@texmath{n}.  By induction on n. In the @texmath{0} case, each
@texmath{0} and @texmath{1} are both mapped to the empty set. In the
inductive step, the trace from @texmath{0} to @texmath{2*n} maps
@texmath{0} and @texmath{1} both to some set @texmath{s}.  and then
indexing @texmath{2*n} indexes the left enumeration at @texmath{n} (by
the "or l" rule) and indexing @texmath{2*n+1} indexes the right
enumeration at @texmath{n}, so the final trace maps both @texmath{0}
and @texmath{1} to @texmath{\{n\}\cup s}.
@qed
}
The Theorem in the coq model is named @racket[SumFair]. 

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


A fair generalization to @texmath{k} arguments is a straightforward
extension. Instead of checking parity and dividing by @texmath{2},
take the quotient with remainder of @texmath{n} with @texmath{k}.
This gives you the fair order illustrated on @texmath{3} arguments in
@figure-ref["fig:disj-sum"], where you use each argument at the same
index before moving to the next one.

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