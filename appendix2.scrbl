#lang scribble/base
@(require scribble/core scriblib/figure
          "model.rkt")

@title[#:tag "sec:appendix2"]{Appendix 2: Formal Semantics}

@(element (style "newpage" '()) '())

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure)]

@Figure-ref["fig:semantics"] shows a formal model of a
subset of our enumerators. It covers only some of the
combinators any considers only infinite enumerations.
The figure defines of the relation @sr[|@|].
It relates an enumeration and an index to the value that
the enumeration produces at the index. The @sr[from-nat]
function treats the first and third positions in the
relation as inputs and produces the middle position. The 
@sr[to-nat] function treats the first and second positions
as inputs and produces the last position.

The @sr[nat/e] enumeration is in the bottom right; it is
just the identity. The two rules in the top of the figure
show how @sr[sum/e] works; if the number is even we use the
left enumeration and if it is odd, we use the right one. It
is simpler than @sr[disj-sum/e] because it forces the
choice to be evident in the resulting enumeration instead of
allowing user-specified predicates. The two @sr[cons/e]
rules in the middle are the most complex. They enumerate in
the order discussed in @secref["sec:enum"], walking in ever
larger squares starting at the origin. The ``x'' rule walks
horizontally and the ``y'' rule walks vertically. The two 
@sr[map/e] rules cover the ways the implementation uses the
two halves of the bijection. It uses the ``in'' rule with 
@sr[from-nat] and the ``out'' rule with @sr[to-nat].
Finally, the @sr[dep/e] rule exploits @sr[cons/e] to get two
indicies. (This variant of @sr[dep/e] enumerates in a slightly different
order than the one in our implementation, but the rule for this one
is clearer.)