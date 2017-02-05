#lang scribble/base

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          data/enumerate/lib
          plot
          scriblib/figure
          (only-in scribble/core element style)
          redex/pict
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair-combinators"]{Fair Combinators}

@figure["fig:biased-pair-pict" "Biased Pair Order"]{
  @centered{@biased-cons-pict[]}
}


Once we know that nesting pairs is not going to be fair in
general, how do we define a fair tupling operation? As we
saw in @secref["sec:fair-informal"], we cannot simply nest
the pairing operation because the outermost pair evenly
divides the input between its two argument enumerations,
even if there is a nested pair on one side, but not on the
other side.

Our approach to fair @texmath{n} dimensional tuples is to
build a biased pairing operation that does not divide the
input evenly, but instead divides it in the ratio @texmath{1:n},
in expectation that left-hand side of the pair will have
one sub-enumeration and the right-hand side of the pair
will have @texmath{n}.

This is the formula for the tuple at position @texmath{z} in
the enumeration of pairs with bias of @texmath{n} on the
right-hand side of the pair:
@(element (style "Pairmn" '()) '())
@Figure-ref["fig:biased-pair-pict"] shows the first few entries
of the pair that has a @texmath{1:2} bias.

The combinatorially-inclined reader may wonder why we do not use the classic Cantor
pairing function.
The two bijections are similar; they are both quadratic
functions with geometric interpretations.
@citet[elegant-pairing-function]'s traces out the
edges of squares and Cantor's traces out the bottoms
of triangles. Importantly, they are both fair (but
with different equilibrium points).

For enumerations we are primarily concerned with the other
direction of the bijection, since that is the one used to generate
terms. In the pairing case, the Cantor function has a fairly
straightforward inverse, but its generalization does not. This is
the generalization of the cantor pairing function to length
@texmath{k} tuples:
@centered{@raw-latex{\vspace*{-.02in}}
           @raw-latex{\textit{cantor\_tuple}$(n_1,n_2,\ldots,n_k) =$}
           @raw-latex{\vspace*{.05in}}
@raw-latex{${{k-1+n_1+\cdots+n_k}\choose{n}}+\cdots+{{1+n_1+n_2}\choose{2}} +
{{n_1}\choose{1}}$}}
We can easily define an inefficient (but correct) way to compute
the inverse by systematically trying every tuple by using a different untupling function, applying the
original @raw-latex{\textit{cantor\_tuple}} function to see if it was the
argument given. @citet[inverting-cantor-n-tupling] gives
the best known algorithm that shrinks the search space considerably, 
but the algorithm there is still a search procedure, and we found it
too slow to use in practice. That said, our library implements 
@citet[inverting-cantor-n-tupling]'s algorithm (via 
a keyword argument to @racket[cons/e] and @racket[list/e]), in
case someone finds it useful.

The @racket[or/e] enumeration's fairness follows a similar, but much
simpler pattern. In particular, the binary @racket[or/e] is fair
because it alternates between its arguments.
As with pairing, extending @racket[or/e] to an @texmath{n}-ary combinator 
via nested calls of the binary combinator is unfair.
Fixing this enumeration is straightforward;
divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use and the quotient
to determine what to index into the enumeration with.
