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
          "model/model.rkt"
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
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

The simplest rule is for @sr[natural/e], in the middle on the left; it is
just the identity. The two rules in the top of the figure
show how @sr[or/e] works; if the number is even we use the
left enumeration and if it is odd, we use the right one. The two @sr[cons/e]
rules are the most complex. They enumerate in
the order discussed in @secref["sec:enum"], walking in ever
larger squares starting at the origin. The ``x'' rule walks
horizontally and the ``y'' rule walks vertically. The condition
in the first premise controls which rule applies. The two 
@sr[map/e] rules cover the ways the implementation uses the
two halves of the bijection. It uses the ``in'' rule with 
@sr[from-nat] and the ``out'' rule with @sr[to-nat].
The @sr[dep/e] rule exploits @sr[cons/e] to get two indicies.

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
       @sr[n] and checking the conditions in on
       @sr[n] in the premises of when there are
       multiple rules for a given @sr[e]. Computing the
       @sr[T] argument is straightforward.
       The proof @tt{Enumerates_from_dec} in the supplementary
       material gives the algorithm and @tt{Enumerates_from_fun}
       shows the answer it produces is unique.}

@theorem{For all @sr[e], @sr[v], there exists 
         a @sr[T] and a unique @sr[n] such that @sr[(|@| e n v T)],
         or there are no @sr[n] such that @sr[(|@| e n v T)],
         and we can compute either the existential witness of @sr[n] or
         its absence.}
@proof{As with the previous theorem, we recursively process
       the rules to compute @sr[n], but this is complicated
       by the fact that we need inverse functions for the 
       formulas in the premises of the rules to go from the
       given @sr[n] to the one to use in the recursive call,
       but these inverses exist.
       The proof @tt{Enumerates_to_dec} in
       the supplementary material gives the algorithm
       and the proof @tt{Enumerates_to_fun} shows the answer
       is unique (when it exists).}

Although we don't prove it formally, the situation when there is no
witness corresponds to the situation where the value that 
we are attempting to convert to a number does not match the contract
in the enumeration in our implementation.

We use these two results to connect the Coq code to our implementation.
Specifically, we use Coq's @tt{Eval} @tt{compute} facility to print out
specific values of the enumeration at specific points and then
compare that to what our implementation produces. Also, the content
of @figure-ref["fig:semantics"] is automatically generated from a Redex
model and we also test the Redex model against the Coq model in
the same manner.

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

We present high-level overviews of proofs of fairness and unfairness
in the following sections. We have mechanized many of these proofs in
coq using a formalism very similar to that in
@Figure-ref["fig:semantics"]. The main difference in the coq model is
that traces are represented as a 4-tuple of sets of natural numbers
rather than functions from natural numbers to sets of naturals. We
will note which proofs have been formalized as we go.


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


@theorem{@racket[cons/e] is Fair}
@proof{
Our equilibria points are @texmath{n^2} for every natural number
@texmath{n}. First, it can be shown that tracing from @texmath{n^2} to
@texmath{(n+1)^2} produces a trace that maps @texmath{0} and
@texmath{1} to the set @texmath{\{0,\ldots,n\}}. Then we can prove
that tracing from @texmath{0} to @texmath{n^2} maps @texmath{0} and
@texmath{1} to @texmath{\bigcup_{m=0}^n\{0,\ldots,n-1\}} and the result
then holds by straightforward induction on @texmath{n}.
@qed
}
The theorem is named @racket[PairFair] in the coq model.

The naive tripling combinator @racket[triple/e] that uses nested calls
to @racket[cons/e], as defined before, is unfair.
@theorem{@racket[triple/e] is unfair}
@proof{
For any natural @texmath{n \ge 16}, there exist natural numbers
@texmath{m, p} such that @texmath{m^2 \le n < p^4} and @texmath{p < m}.
Then a complete trace from @texmath{0} to @texmath{n} will map
@texmath{0} to a set that includes everything in
@texmath{\{0,\ldots,m\}}, but will map @texmath{1} (and @texmath{2})
to sets that are subsets of @texmath{\{0,\ldots,p\}}. Since @texmath{p < m},
these sets are different, so @racket[triple/e] is unfair.
@qed
}
The theorem is named @racket[NaiveTripleUnfair] in the coq model.

