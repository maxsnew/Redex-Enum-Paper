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

In other words, we can view
@citet[elegant-pairing-function]'s enumeration function as
enumerating all @texmath{(i,j)} whose maximum is @texmath{
 0}, then @texmath{1}, then @texmath{2}, etc. This is what
gives it a square-like pattern. Since we want to bias the
right argument by @texmath{n}, we can enumerate the pairs in
a similar manner, but considering the @texmath{n}-th
root of the right coordinate, not just its plain value.
We call this the ``biased maximum''; more precisely,
the biased maximum of the pair @texmath{(i,j)} is
@texmath{\max(i+1,\lceil (j+1)^{1/n}\rceil)} and we first
enumerate all pairs where the biased maximum is 1, then 2, then 3, etc.

@Figure-ref["fig:biased-pair-pict"] shows the first few
entries of the enumeration order for pairs that has a
@texmath{1:2} bias. The diagram is reversed (the
y-coordinate is horizontal and the x-coordinate is vertical)
so it fits more easily on the page. The first point
@texmath{(0,0)} is the only point where biased maximum is 1; the next seven points are those
where the biased maximum is always 2, etc. With a pair
that has a @texmath{1:2} bias, the biased maximum
will be the same in the interval @texmath{[3^k,3^{k+1})}, for any
value of @texmath{k}. In general, with a @texmath{1:n} biased
pair enumerator, any pair in the interval
@texmath{[(n+1)^k,(n+1)^{k+1})} has the same biased maximum, namely @texmath{k+1}.

This is an explicit formula for the tuple at position @texmath{z} in
the enumeration of pairs with bias of @texmath{1:n}:
@(element (style "Pairmn" '()) '())

To define a fair @texmath{n}-dimensional tupling function, we
can systematically exploit the bias. Once we have a fair
@texmath{n}-dimensional tuple enumeration, we can make a
@texmath{n+1}-dimensional fair tuple enumeration by pairing the
@texmath{n}-dimensional tuple enumeration with the new
enumeration for the @texmath{n}th enumeration using a
biased @texmath{1:n} pairing.

The combinatorially-inclined reader may wonder why our tupling is
based on @citet[elegant-pairing-function]'s pairing function and not
the classic Cantor pairing function.
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

Furthermore, @citet[elegant-pairing-function]'s pairing function lends
itself quite easily to a biased formulation, since enumerating
rectangles is a simple modification from enumerating squares.  We
leave it to future work to find a similar biased formulation of the
Cantor pairing function.

The @racket[or/e] enumeration's fairness follows a similar, but much
simpler pattern. In particular, the binary @racket[or/e] is fair
because it alternates between its arguments.
As with pairing, extending @racket[or/e] to an @texmath{n}-ary combinator 
via nested calls of the binary combinator is unfair.
Fixing this enumeration is straightforward;
divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use and the quotient
to determine what to index into the enumeration with.
