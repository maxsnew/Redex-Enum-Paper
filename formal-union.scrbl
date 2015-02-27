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

@theorem{@racket[or-three/e is unfair]}
@proof{
To show something is unfair, we show that after a certain point, there
are no equilibria. For any @texmath{n}, the trace evaluated at
@texmath{0} will always include a number near
@texmath{\lfloor{(n-1)/2}\rfloor}, but everything in the set that is
the trace evaluated at @texmath{1} or @texmath{2} will be less than
@texmath{\lceil{n/4}\rceil}. For sufficiently large @texmath{n},
@texmath{\lfloor{(n-1)/2}\rfloor > \lceil{n/4}\rceil} so these sets
are not equal.
@qed
}
The theorem in the coq model is @racket[NaiveSum3Unfair].
