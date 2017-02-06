#lang scribble/base

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          racket/format
          racket/set
          data/enumerate/lib
          plot
          scriblib/figure
          redex/reduction-semantics
          redex/pict
          "model/redex-model.rkt"
          "model/redex-model-typesetting.rkt"
          "model/redex-model-test.rkt"
          "util.rkt")

@title[#:tag "sec:fair-formal"]{Enumeration Semantics}

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure1)]

@figure*["fig:semantics-helpers" @list{Semantics of Enumeration Combinators, Continued}
         (semantics-figure2)]

@Figure-ref["fig:semantics"] shows a formal model of our enumerations.
The model differs from our implementation in the way it handles
unions (forcing them to be disjoint via @sr[inl] and @sr[inr])
and by having a type system instead of using contracts to describe
the sets of values that an enumeration produces.

The relation 
@sr[|@|] defines the semantics of the enumerations. It relates an enumeration and an index to the
value that the enumeration produces at the index. 
The @sr[T] that follows the vertical bar is used in the definition
of fairness; we explain it after introducing the basics of the model. The 
@sr[from-nat] and @sr[to-nat] functions are derived from 
@sr[|@|] by treating either the value or
index argument as given and computing the other one.
The contents of @Figure-ref["fig:semantics"] are automatically generated
from a Redex model and we also built a Coq model of a subset of this 
semantics. All of the theorems stated in this section
are proven with respect to the Coq model. The Redex model,
Coq model, and our implementation are all tested against each other.

The upper right of the figure has the simplest rule,
the one for @sr[(below/e n+)]; it is just the identity.
Below the @sr[below/e] rule is the @sr[fix/e] rule. The
@sr[fix/e] combinator in the model is like @racket[delay/e]
from the implementation, except it
provides an explicit name for the enumeration. The rule
uses substitution (the definition of substitution is standard
and is omitted for brevity).

The next two rules, reading straight down the figure, are the @sr[dep/e] rules.
The @sr[dep/e] combinator is a simplified, functional interface
to the @racket[cons/de] combinator. It accepts an
enumeration and a function from elements of the first
enumeration to new enumerations. It produces pairs where the
first position of the pair comes from the first enumeration
and the second position's elements come from the enumeration
returned by passing the first element of the pair to the
given function. The @sr[dep/e] rule exploits @sr[cons/e] to
get two indices when it deals with infinite enumerations and
uses @mf-name{sum_up_to} for finite enumerations (defined
at the bottom of @figure-ref["fig:semantics-helpers"]).

The first rule underneath the boxed grammar is the
@sr[map/e] rule, showing how its bijection is used. The next
four rules govern the @sr[or/e] combinator. These rules work
by alternating between the two enumerations until one runs
out (in the case that it is finite), and then they just use
the other enumeration. The upper two @sr[or/e] rules cover
the case where neither has yet run out. The lower two cover
the situation where of the arguments was finite and the
enumeration has already produced all of those elements. The
rules with ``l'' in the name end up producing a value from
the left enumeration and the rules with an ``r'' produce a
value from the right.

The @sr[cons/e] rule uses the @mf-name{unpair} function, shown
in @figure-ref["fig:semantics-helpers"].
The @mf-name{unpair} function accepts the sizes of the two enumerations,
computed by the size function in the middle of @figure-ref["fig:semantics-helpers"]
(written using double vertical bars), and the index.
The function maps indices as discussed in @secref["sec:enum"].

To the right of the @sr[cons/e] rule are the rules for the @sr[except/e]
combinator, which behaves as discussed in @secref["sec:enum"], one rule for the
situation where the value is below the excepted value and
one for where it is above.

We return to the rule for @sr[trace/e] shortly, and the 
last rule is an unfair pairing operation using the
bijection from the introduction.

The Coq model is simpler than the model presented here and
the model presented here is simpler than our implementation.
The primary difference between the three is in the kinds of values that
are enumerated. In our implementation, any value that can be
captured with a contract in Racket's contract system can be
enumerated. In the model presented here, we restrict those
values to the ones captured by @sr[τ], and in the Coq model
restrict that further by eliminating recursive types, subtraction
types, and finite types. The implementation does not have
a type system; the role of types played by the contract system instead.
Contracts give us additional flexibility that ordinary type systems
do not have, allowing us to maintain the invariant that the
contract describes the precise set of values that can be enumerated,
even for enumerations of only positive numbers, or non-empty lists, etc.
Having these precise contracts has proven helpful in practice as we
debug programs that use the enumeration library.

The implementation also has many more combinators than the
ones presented here, but they are either derivable from
these or require only straightforward extensions. The Coq
model has the combinators in @figure-ref["fig:semantics"],
except for the @sr[fix/e] combinator and the @sr[except/e]
combinator. There are no other differences between the Coq
model and the model in the paper. In general, the Coq model
is designed to be just enough for us to state and prove some
results about fairness whereas the model presented in the paper
is designed to provide a precise explanation of our enumerations.

The typing rules for values are given in the box at the
bottom right of @figure-ref["fig:semantics"], and the
@mf-name{ty} function maps enumerators to the type of values
that it enumerates. All enumerators enumerate all of the
values of their types.

Before we define fairness, however, we first need to prove that
the model actually defines two functions.
@theorem{
 For all @sr[e] (in the Coq model), @sr[n], there exists
 a unique @sr[v] and @sr[T] such that @sr[(|@| e n v T)]
 and @sr[(⊢v v (ty e))], and we can compute @sr[v] and @sr[T].
}
@proof{The basic idea is that you can read the value off
       of the rules recursively, computing new values of
       @sr[n]. In some cases there are multiple rules that apply
       for a given @sr[e], but the conditions on
       @sr[n] in the premises ensure there is exactly one rule
       to use. Computing the
       @sr[T] argument is straightforward.
       The full proof is given as @tt{Enumerates_from_dec_uniq} in the supplementary
       material.}

@theorem{
 For all @sr[e] (in the Coq model), @sr[v],
 if @sr[(⊢v v (ty e))], then there exists 
 a unique @sr[T] and @sr[n] such that @sr[(|@| e n v T)].
}
@proof{As before, we recursively process
 the rules to compute @sr[n]. This is complicated by the
 fact that we need inverse functions for the formulas in the
 premises of the rules to go from the given @sr[n] to the
 one to use in the recursive call, but these inverses
 exist. The full proof is given as
 @tt{Enumerates_to_dec_uniq} in the supplementary material,
 and it includes proofs of the formula inverses.}

Although we don't prove it formally, the situation where
the @sr[(⊢v v (ty e))] condition does not hold in the
second theorem corresponds to the situation where the value
that we are attempting to convert to a number does not match
the contract in the enumeration in our implementation (i.e.,
a runtime error).

We use these two results to connect the Coq code to our implementation.
Specifically, we use Coq's @tt{Eval} @tt{compute} facility to print out
values of the enumeration at specific points and then
compare that to what our implementation produces. This is the same
mechanism we use to test our Redex model against the Coq model.
The testing code is in the supplementary material.

To define fairness, we need to be able to trace how an enumeration
combinator uses its arguments, and this is the purpose of the
@sr[trace/e] combinator and the @sr[T] component in the 
semantics. These two pieces work together to trace 
where a particular enumeration has been sampled. Specifically,
wrapping an enumeration with @sr[trace/e] means that it should be
tracked and the @sr[n] argument is a label used to identify 
a portion of the trace. The @sr[T] component is the current trace; it
is a function that maps the @sr[n] arguments in the @sr[trace/e]
expressions to sets of natural numbers indicating which naturals
the enumeration has been used with.

Furthermore, we also need to be able to collect all of the
traces for all naturals up to some
given @sr[n]. We call this the ``complete trace up to @sr[n]''.
So, for some enumeration expression @sr[e], the complete
trace up to @sr[n] is the pointwise union of all of the @sr[T] components
for @sr[(|@| e i v T)], for all values @sr[v] and @sr[i] strictly 
less than @sr[n].

@(define trace-size 256)
@(define-syntax-rule
   (define-ex x y e)
   (define-values (x y) (values (sr e) (complete-trace (term e) trace-size))))

@(define-ex fair-pair-sr fair-pair-trace
   (cons/e (trace/e 0 (below/e ∞))
           (trace/e 1 (below/e ∞))))
@(define-ex unfair-pair-sr unfair-pair-trace
   (unfair-cons/e (trace/e 0 (below/e ∞))
                  (trace/e 1 (below/e ∞))))
@(unless (equal? (hash-ref fair-pair-trace 0)
                 (hash-ref fair-pair-trace 1))
   (error 'fair-pair-not-equal "(need to revise text that claims otherwise)"))

@(define (show-set s)
   (define eles (set->list s))
   (cond
     [(empty? eles) "∅"]
     [(= (set-count eles) 1)
      (format "{~a}" (set-first eles))]
     [(<= 2 (set-count eles) 4)
      (apply format
             (case (set-count eles)
               [(2) "{~a, ~a}"]
               [(3) "{~a, ~a, ~a}"]
               [(4) "{~a, ~a, ~a, ~a}"])
             (sort (set->list eles)
                   string<?
                   #:key (λ (x) (format "~s" x))))]
     [else
      (define sm (apply min eles))
      (define bg (apply max eles))
      (for ([i (in-range sm (+ bg 1))])
        (unless (set-member? s i)
          (error 'fair-formal.scbrl "got a set that's isn't a contiguous range; doesn't have ~a"
                 i)))
      (format "{x:nat | ~a ≤ x ≤ ~a}" sm bg)]))

For example, the complete trace of
@centered{@fair-pair-sr}
up to @(add-commas trace-size)
maps both @sr[0] and @sr[1] to @(show-set (hash-ref fair-pair-trace 0)),
meaning that the two arguments were explored exactly the same
amount, at least for the first @(add-commas trace-size) elements.
The complete trace of
@centered{@unfair-pair-sr}
up to @(add-commas trace-size), however,
maps @sr[0] to @(show-set (hash-ref unfair-pair-trace 0))
and @sr[1] to @(show-set (hash-ref unfair-pair-trace 1)), where
@sr[unfair-cons/e] is the unfair pairing combinator from the introduction.
This shows that the first argument (traced with the @sr[0]) is explored more
than the second.

We say that an enumeration combinator @texmath{c^k : enum ... \rightarrow enum}
of arity @texmath{k} is fair if, for every
natural number @texmath{m}, there exists a natural number 
@texmath{M > m} such that 
in the complete trace up to @texmath{M} of @texmath{c^k} applied to @sr[(trace/e 1 enum_1)]
@texmath{\cdots} @sr[(trace/e k enum_k)], for any enumerations @sr[enum_1]
to @sr[enum_k], is a function that maps each number between @sr[1] and @sr[k]
to exactly the same set of numbers. Any other combinator is unfair.
In other words, a fair combinator is one where the traces
of its arguments are explored the same amount at an infinite number of points,
namely the values of @texmath{M}. As such, we call the values of 
@texmath{M} the equilibrium points.

We say that a combinator is @texmath{f}-fair if the @texmath{n}-th equilibrium
point is at @texmath{f(n)}.
The Coq model contains this definition only for @raw-latex{$k\in \{2,3,4\}$},
called @tt{Fair2}, @tt{Fair3}, and @tt{Fair4}.

@(define (or/e-trace n)
   (define tr
     (complete-trace (term (or/e (trace/e 0 (below/e ∞)) (trace/e 1 (below/e ∞))))
                     n))
   (unless (equal? (hash-ref tr 0)
                   (hash-ref tr 1))
     (error 'fair-formal.scrbl "expected identical traces for or/e up to ~s, got ~s and ~s"
            n
            (hash-ref tr 0)
            (hash-ref tr 1)))
   (show-set (hash-ref tr 0)))

@theorem{@sr[or/e] is @texmath{\lambda n.\ 2n+2}-fair.}
@proof{
This can be proved by induction on @texmath{n}.
The full proof is @tt{SumFair} in the Coq model.
}
Concretely, this means that the equilibrium points of @sr[or/e]
are @texmath{2}, @texmath{4}, @texmath{6}, @texmath{8}, etc.
Tracing @racket[or/e] up to those points produces the sets
@(or/e-trace 2),
@(or/e-trace 4), 
@(or/e-trace 6), and
@(or/e-trace 8), etc.

@theorem{Using nested @racket[or/e] to construct a three-way enumeration is unfair.}
@proof{

We show that after a certain point, there are no equilibria. For
@texmath{n \ge 8}, there exist natural numbers @texmath{m, p} such
that @texmath{2m \le n < 4p} while @texmath{p < m}. Then a complete
trace from @texmath{0} to @texmath{n} maps @texmath{0} to a set that
contains @texmath{\{0,\ldots,m\}}, but maps
@texmath{1} (and @texmath{2}) to subset of
@texmath{\{0,\ldots,p\}}. Since @texmath{p < m}, these sets are
different. Thus @racket[or-three/e] is unfair.
The full proof is @tt{NaiveSum3Unfair} in the Coq model.
}


@theorem{@sr[cons/e] is @texmath{\lambda n.\ (n+1)^2}-fair.}
@proof{
First, we show that tracing from @texmath{n^2} to
@texmath{(n+1)^2} produces a trace that maps @texmath{0} and
@texmath{1} to the set @texmath{\{0,\ldots,n\}}. Then we can prove
that tracing from @texmath{0} to @texmath{n^2} maps @texmath{0} and
@texmath{1} to @texmath{\{0,\ldots,n-1\}} and the result
then holds by induction on @texmath{n}.
The full proof is @tt{PairFair} in the Coq model.
}

@theorem{@racket[triple/e] from @secref["sec:fair-informal"] is unfair.}
@proof{
For any natural @texmath{n \ge 16}, there exist natural numbers
@texmath{m, p} such that @texmath{m^2 \le n < p^4} and @texmath{p < m}.
Then a complete trace from @texmath{0} to @texmath{n} will map
@texmath{0} to a set that includes everything in
@texmath{\{0,\ldots,m\}}, but will map @texmath{1} (and @texmath{2})
to sets that are subsets of @texmath{\{0,\ldots,p\}}. Since @texmath{p < m},
these sets are different, so @sr[triple/e] is unfair.
The full proof is @tt{NaiveTripleUnfair} in the Coq model.
}

@theorem{The pairing operator @sr[unfair-cons/e],
 defined using the unfair bijection
 from the introduction, is unfair.}
@proof{
A complete trace from @texmath{0} to @texmath{n}
contains all of the values from @texmath{0} to
@texmath{\lfloor n/2+1\rfloor} in the first component and
all of the values from @texmath{0} to
@texmath{\lfloor\log_2(n)\rfloor+1} in the second component.
For any @texmath{n}
greater than @texmath{8}, the first component will always
have more values than the second component and thus there
will be no equilibrium points after @texmath{8}.
The full proof is @tt{UnfairPairUnfair} in the Coq model.
}
