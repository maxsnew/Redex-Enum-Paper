#lang scribble/base
@(require scribble/core scriblib/figure
          "model.rkt")

@title[#:tag "sec:appendix2"]{Appendix 2: Formal Semantics}

@(element (style "newpage" '()) '())

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure)]

@Figure-ref["fig:semantics"] shows a formal model of a
subset of our enumerators. It defines of the relation 
@sr[|@|], which relates an enumeration and an index to the
value that the enumeration produces at the index. The 
@sr[from-nat] and @sr[to-nat] functions are derived from 
@sr[|@|] by treating either the value or
index argument as given and computing the other one.

The @sr[nat/e] enumeration is in the bottom right; it is
just the identity. The two rules in the top of the figure
show how @sr[sum/e] works; if the number is even we use the
left enumeration and if it is odd, we use the right one. The two @sr[cons/e]
rules in the middle are the most complex. They enumerate in
the order discussed in @secref["sec:enum"], walking in ever
larger squares starting at the origin. The ``x'' rule walks
horizontally and the ``y'' rule walks vertically. The two 
@sr[map/e] rules cover the ways the implementation uses the
two halves of the bijection. It uses the ``in'' rule with 
@sr[from-nat] and the ``out'' rule with @sr[to-nat].
Finally, the @sr[dep/e] rule exploits @sr[cons/e] to get two
indicies.

The model is different from our implementation in three ways.
First, it covers only some of the combinators and
only infinite enumerations. Second, @sr[disj-sum/e]
allows user-specified predicates instead of forcing disjointness
by construction like @sr[sum/e]. Third, @sr[dep/e] uses a slightly different
ordering than the model (we consider this a bug in the implementation and will fix it).
