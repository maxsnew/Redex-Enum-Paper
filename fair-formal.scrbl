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

@title[#:tag "sec:fair-formal"]{Enumeration and Fairness Semantics}

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure)]

@Figure-ref["fig:semantics"] shows a formal model of a
subset of our enumerators. It defines of the relation 
@sr[|@|], which relates an enumeration and an index to the
value that the enumeration produces at the index. 
The @sr[T] that follows the vertical bar is used in the definition
of fairness; ignore it for now. The 
@sr[from-nat] and @sr[to-nat] functions are derived from 
@sr[|@|] by treating either the value or
index argument as given and computing the other one.

The @sr[natural/e] enumeration is in the bottom left; it is
just the identity. The two rules in the top of the figure
show how @sr[or/e] works; if the number is even we use the
left enumeration and if it is odd, we use the right one. The two @sr[cons/e]
rules in the middle are the most complex. They enumerate in
the order discussed in @secref["sec:enum"], walking in ever
larger squares starting at the origin. The ``x'' rule walks
horizontally and the ``y'' rule walks vertically. The condition
in the first premise controls which rule applies. The two 
@sr[map/e] rules cover the ways the implementation uses the
two halves of the bijection. It uses the ``in'' rule with 
@sr[from-nat] and the ``out'' rule with @sr[to-nat].
The @sr[dep/e] rule exploits @sr[cons/e] to get two indicies.

The model is different from our implementation in three ways.
First, it covers only some of the combinators and
only infinite enumerations. Second, @sr[or/e] in our implementation
allows user-specified predicates instead of forcing disjointness
by construction like @sr[or/e] in the model. Nevertheless, it
is enough for us to state and and prove results about fairness.

To define fairness, we need to be able to trace how an enumeration
combinator uses its arguments, and this is the purpose of the
@sr[trace/e] combinator and the @sr[T] component in the 
semantics. These two pieces work together to trace the arguments
that a particular enumeration has been used at. Specifically,
wrapping an enumeration with @sr[trace/e] means that it should be
tracked and the @sr[n] argument is a label used to identify 
a portion of the trace. The @sr[T] component is the trace; it
is a function that maps the @sr[n] arguments in the @sr[trace/e]
expressions to sets of natural numbers indicating which naturals
the enumerator has been used with.

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

@include-section["formal-union.scrbl"]
@include-section["formal-tuple.scrbl"]
