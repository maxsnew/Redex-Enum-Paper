#lang scribble/base
@(require scribble/core scriblib/figure
          "model.rkt")

@title[#:tag "sec:appendix2"]{Appendix 2: Formal Semantics}

@(element (style "newpage" '()) '())

@figure*["fig:semantics" @list{Semantics of Enumeration Combinators} (semantics-figure)]

@Figure-ref["fig:semantics"] shows a formal model of a
subset of our enumerators. It does not cover all of the
combinators nor does it cover finite enumerations.

The figure contains a definition of the relation @sr[|@|].
It relates an enumeration and an index to the value that
the enumeration produces at the index. The @sr[from-nat]
function treats the first and third positions in the
relation as inputs and produces the middle position. The 
@sr[to-nat] function treats the first and second positions
as inputs and produces the last position.

The simplest case is in the bottom right; it shows that 
@sr[nat/e] is just the identity. The two rules in the top of
the figure show how @sr[sum/e] works; if the number is even
we use the left enumeration and if it is odd, we use the
right one. The two @sr[cons/e] rules in the middle are the
most complex. They enumerate in the order discussed in 
@secref["sec:enum"], walking in ever larger squares starting
at the origin. The ``x'' rule walks horizontally and the
``y'' rule walks vertically. The two @sr[map/e] rules cover
the ways the implementation uses the two halves of the
bijection. It uses the ``in'' rule with @sr[from-nat] and
the ``out'' rule with @sr[to-nat]. Finally, the @sr[dep/e]
rule exploits @sr[cons/e] to get two indicies.