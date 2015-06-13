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
          "model/redex-model-typesetting.rkt"
          "util.rkt")

@title[#:tag "sec:fair-formal"]{Enumeration Semantics}

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure)]

@Figure-ref["fig:semantics"] shows a formal model of a
subset of our enumerations. It defines of the relation 
@sr[|@|], which relates an enumeration and an index to the
value that the enumeration produces at the index. 
The @sr[T] that follows the vertical bar is used in the definition
of fairness; ignore it for now. The 
@sr[from-nat] and @sr[to-nat] functions are derived from 
@sr[|@|] by treating either the value or
index argument as given and computing the other one.
The contents of @Figure-ref["fig:semantics"] are automatically generated
from a Redex model and we also build a Coq model of this 
semantics. All of the theorems stated in this section
are proven with respect to the Coq model and the Redex model,
Coq model, and our implementation are all tested against each other.

The simplest rule is for @sr[natural/e], in the bottom right; it is
just the identity. The two rules just above it
show how @sr[or/e] works; if the number is even we use the
left enumeration and if it is odd, we use the right one. The two @sr[cons/e]
rules at the top of the figure are the most complex. They enumerate in
the order discussed in @secref["sec:enum"], walking in ever
larger squares starting at the origin. The ``x'' rule walks
horizontally and the ``y'' rule walks vertically. The condition
in the first premise controls which rule applies. The
@sr[map/e] rule shows how the bijection is used.
The @sr[dep/e] rule exploits @sr[cons/e] to get two indicies.
We return to the rule for @sr[trace/e] shortly.

The model simplifies our implementation in three ways.
First, it covers only some of the combinators and
only infinite enumerations. 
Second, the enumerations do not have contracts.
Third, @sr[or/e] in our implementation
allows user-specified predicates instead of forcing disjointness
by construction like @sr[or/e] in the model. Nevertheless, it
is enough for us to state and and prove some results about fairness.

Before we define fairness, however, we first need to prove that
the model actually defines two functions. 
@theorem{For all @sr[e], @sr[n], there exists 
         a unique @sr[v] and @sr[T] such that @sr[(|@| e n v T)],
         and we can compute @sr[v] and @sr[T].}
@proof{The basic idea is that you can read the value off
       of the rules recursively, computing new values of
       @sr[n]. In some cases there are multiple rules that apply
       for a given @sr[e], but the conditions on
       @sr[n] in the premises ensure there is exactly one rule
       to use. Computing the
       @sr[T] argument is straightforward.
       The full proof is given as @tt{Enumerates_from_dec_uniq} in the supplementary
       material.}

@theorem{For all @sr[e], @sr[v], there exists 
         a unique @sr[T] and @sr[n] such that @sr[(|@| e n v T)],
         or there are no @sr[n] or @sr[T] such that @sr[(|@| e n v T)],
         and we can compute either the existential witness of @sr[n] or
         its absence.}
@proof{As with the previous theorem, we recursively process
       the rules to compute @sr[n], but this is complicated
       by the fact that we need inverse functions for the 
       formulas in the premises of the rules to go from the
       given @sr[n] to the one to use in the recursive call,
       but these inverses exist.
       The full proof is given as @tt{Enumerates_to_dec_uniq} in
       the supplementary material.}

Although we don't prove it formally, the situation when there is no
@sr[n] in the second theorem corresponds to the situation where the value that 
we are attempting to convert to a number does not match the contract
in the enumeration in our implementation.

We use these two results to connect the Coq code to our implementation.
Specifically, we use Coq's @tt{Eval} @tt{compute} facility to print out
specific values of the enumeration at specific points and then
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
numbers traced of an enumeration for all naturals up to some
given @sr[n]. So, for some enumeration expression @sr[e], the complete
trace up to @sr[n] is the union of all of the @sr[T] components
for @sr[(|@| e i v T)], for all values @sr[v] and @sr[i] strictly 
less than @sr[n].

We say that an enumeration combinator @raw-latex{$c^k : enum ... \rightarrow enum$}
of arity @raw-latex{$k$} is fair if, for every
natural number @raw-latex{$m$}, there exists a natural number 
@raw-latex{$M > m$} such that 
in the complete trace of @raw-latex{$c^k$} applied to @sr[(trace/e 1 enum_1)]
@raw-latex{$\cdots$} @sr[(trace/e k enum_k)], for any enumerations @sr[enum_1]
to @sr[enum_k], is a function that maps each number between @sr[1] and @sr[k]
to exactly the same set of numbers. Any other combinator is unfair.
The Coq model contains this definition only for @raw-latex{$k\in \{2,3,4\}$},
called @tt{Fair2}, @tt{Fair3}, and @tt{Fair4}.

@theorem{@racket[or/e] is fair.}
@proof{
The equilibrium points are at @texmath{2*n} for each
@texmath{n} and this can be proved by induction on @texmath{n}.
The full proof is @tt{SumFair} in the Coq model.
}

@theorem{@racket[or-three/e] from @secref["sec:fair-informal"] is unfair.}
@proof{

We show that after a certain point, there are no equilibria. For
@texmath{n \ge 8}, there exist natural numbers @texmath{m, p} such
that @texmath{2m \le n < 4p} while @texmath{p < m}. Then a complete
trace from @texmath{0} to @texmath{n} maps @texmath{0} to a set that
contains @texmath{\{0,\ldots,m\}}, but on the other hand maps
@texmath{1} (and @texmath{2}) to subset of
@texmath{\{0,\ldots,p\}}. Since @texmath{p < m}, these sets are
different. Thus @racket[or-three/e] is unfair.
The full proof is @tt{NaiveSum3Unfair} in the Coq model.
}


@theorem{@racket[cons/e] is fair}
@proof{
Our equilibria points are @texmath{n^2} for every natural number
@texmath{n}. First, it can be shown that tracing from @texmath{n^2} to
@texmath{(n+1)^2} produces a trace that maps @texmath{0} and
@texmath{1} to the set @texmath{\{0,\ldots,n\}}. Then we can prove
that tracing from @texmath{0} to @texmath{n^2} maps @texmath{0} and
@texmath{1} to @texmath{\bigcup_{m=0}^n\{0,\ldots,n-1\}} and the result
then holds by induction on @texmath{n}.
The full proof is @tt{PairFair} in the Coq model.
}

@theorem{@racket[triple/e] from @secref["sec:fair-informal"] is unfair}
@proof{
For any natural @texmath{n \ge 16}, there exist natural numbers
@texmath{m, p} such that @texmath{m^2 \le n < p^4} and @texmath{p < m}.
Then a complete trace from @texmath{0} to @texmath{n} will map
@texmath{0} to a set that includes everything in
@texmath{\{0,\ldots,m\}}, but will map @texmath{1} (and @texmath{2})
to sets that are subsets of @texmath{\{0,\ldots,p\}}. Since @texmath{p < m},
these sets are different, so @racket[triple/e] is unfair.
The full proof is @tt{NaiveTripleUnfair} in the Coq model.
}

