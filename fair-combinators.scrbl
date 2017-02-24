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

In other words, we can view @citet[elegant-pairing-function]'s
enumeration function as enumerating all @texmath{(i,j)} whose maximum
is @texmath{0}, then @texmath{1}, then @texmath{2}, etc. This is what
gives it a square-like pattern. If instead we want to bias the right
argument by @texmath{n}, we can enumerate all @texmath{(i,j)} where
@texmath{\max(i,\lfloor j^{1/n}\rfloor) = 0} then 1, then 2, etc.

Then instead of equilibrium points, we have "weighted equilibria", for
a @texmath{1:n} pairing function we get that the @texmath{k}th
weighted equilibrium is at index @texmath{k^{n+1}} and the enumerated
pairs from @texmath{0} to @texmath{k^{n+1}} are all pairs
@texmath{(i,j)} where @texmath{i < k} and @texmath{j < k^n}.

This is an explicit formula for the tuple at position @texmath{z} in
the enumeration of pairs with bias of @texmath{n} on the
right-hand side of the pair:
@(element (style "Pairmn" '()) '())
@Figure-ref["fig:biased-pair-pict"] shows the first few entries
of the pair that has a @texmath{1:2} bias.
While that is clearly unfair, when the second component is an unbiased
pair, then the overall result is a fair three tuple.

We can then define a fair @texmath{n}-dimensional tupling function
inductively using biased pairing by defining @texmath{1}-dimensional
tupling to be the appropriate wrapping of the identity and
@texmath{n+1}-dimensional tupling to be the biased @texmath{1:n}
pairing of the first enumaration and the recursive
@texmath{n}-dimensional tupling.

@theorem{
@texmath{n}-dimensional tupling as defined above is @texmath{\lambda k. k^n - 1}
fair and for every k, the set enumerated by (list/e e_1
... e_n) from 0 to @texmath{k^n - 1} is the set of all lists (x_1
... x_n) where x_i is drawn from e_i at some index @texmath{j_i < k}
}

@proof{
By induction on @texmath{n}.
The @texmath{1} case is trivial, for @texmath{n+1}, note that the set
of all possible lists generated from below a fixed index is the same
as the product of all first elements below a fixed index paired with
all choices of the rest of the list below that index.
Then combining the inductive hypothesis with the remark about weighted
equilibria gives the desired result.
}

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
