#lang scribble/sigplan

@(require pict
          scribble/manual
          racket/draw
          data/enumerate/lib
          plot
          scriblib/figure
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title{Pairing and Tupling}

The combinatorially-inclined reader may have noticed in our
description of @racket[cons/e] that we did not use the classic Cantor
pairing function for our bijection, which can be interpreted as a more
triangular grid walk:@centered{@cantor-cons-pict[]}. Instead we use
@citet[elegant-pairing-function]'s bijection, that we refer to as
``boxy'' pairing. The pairing functions are given by

@centered{@raw-latex{$cantor\_pair(m, n) = \frac{(n+m)(n+m+1)}{2} + m$}}
@centered{@raw-latex{$box\_pair(m, n) = \begin{cases} x^2+x+y &\mbox{if } x\ge y\\ x+y^2   &\mbox{if } x < y \end{cases}$}}

The two bijections are quite similar; they are both quadratic
functions with similar geometric interpretations: boxy traces out the
edges of increasingly large squares and Cantor traces out the bottoms
of increasingly large triangles. This is exactly why they are both
fair. When enumerating, each ``layer'' uses its arguments equally so
enumerating each layer in turn is fair. An algebraic way to state this
is that the Cantor pairing function is monotonic in the sum of its 2
arguments, whereas the boxy pairing function is monotonic in the max
of its 2 arguments. The Cantor function first enumerates all pairs
with sum 0, then those with sum 1 and so on, whereas the boxy does the
same for the maximum.

This point of view also leads to natural generalizations to
n-tuples. Generalized boxy enumerates in order of the maximum of its n
arguments, tracing out the outer faces of an n cube. Generalized
Cantor enumerates in the order of the sum of its arguments, tracing
out the outer faces of an n simplex. By maintaining this ``layering''
property, we ensure that the generalized combinators are also fair.

Despite their conceptual similarity, we found the boxy enumeration
lends itself to a more efficient implementation. To understand why, note
that most combinatorics applications of pairing functions are chiefly
concerned with one half of the bijection: the one from pairs of
natural numbers to natural numbers, defined above.

For enumerations we are primarily concerned with the other
direction of the bijection, since that is the one used to generate
terms. For the pairing case, these functions have fairly
straightforward inverses, but their generalizations do not. This is
the generalization of the cantor pairing function to length
@texmath{k} tuples:
@centered{@raw-latex{$cantor\_tuple(n_1,n_2,\ldots,n_k) =
{{k-1+n_1+\cdots+n_k}\choose{n}}+\cdots+{{1+n_1+n_2}\choose{2}} +
{{n_1}\choose{1}}$}}
We can easily define a highly inefficient (but correct) way to compute
the inverse by trying every natural number, in order, applying the
original @raw-latex{$cantor\_tuple$} function to see if it was the
argument given. The best known algorithm for this
@citet[inverting-cantor-n-tupling] improves on this implementation by
vastly reducing the search space, but the algorithm there is still a
search procedure, and we found it too slow to use in practice.

So how do we generalize boxy pairing to boxy tupling and how do we
compute an efficient inverse? The ``layering'' view gives the
answer. As an example, when we encode @racket[42] with
@racket[cons/e], we first take the square root with remainder, giving
us a root of @racket[6] with a remainder of @racket[8]. The @racket[6]
tells us that we are in the ``layer'' where all pairs have a maximum
element of @racket[6]. The remainder @racket[8] tells us that we are
at the @racket[8]th such pair. Now we need to index at @racket[8] into
an enumeration of lists whose maximum element is @racket[6], which
gives us the pair @racket['(6 . 0)].

To perform the inverse, we take @racket['(6 . 0)] and identify that
its max is @racket[6]. Then pass @racket['(6 . 0)] into the opposite
direction of the enumeration of pairs with max @racket[6], giving us
@racket[8]. We then square @racket[6] and add @racket[8] to get
@racket[42].

The only remaining question is how to enumerate pairs with a given
maximum, say @racket[6]. This is precisely the @racket[6]th layer
(counting from @racket[0]), a row where the first component is
@racket[6] and a column where the second component is @racket[6], a
total of @racket[37] different pairs. Then we split that range in half
and map the first half to the row and the second half to the column.
However, we need not right these formulae out by hand, as we can use a
finite version of @racket[cons/e] and an @racket[append/e] combinator
that appends one enumeration to the end of a finite one.

The key idea is that we find what ``layer'' a value is on and we
bootstrap the implementation with existing implementations of
@racket[cons/e] and @racket[disj-sum/e] for finite enumerations,
giving us both halves of the layer enumeration in one fell
swoop. 

For the boxy ordering, identifying what layer you are on is easy, you
just take the @racket[k]th root when enumerating tuples of length
@racket[k]. Inverting the Cantor pairing function in the same way
would require taking a @racket[k]th-simplicial root.

Enumerating layers can be done recursively. For example when indexing
@racket[(list/e natural/e natural/e natural/e)] at @racket[42] we take
the cube root with remainder and get @racket[3] with a remainder of
@racket[15], so our triple has a maximum of @racket[3] and is the
@racket[15]th such triple. There are @racket[3] faces of the cube
where the maximal value is @racket[3], so to enumerate all values on
the layer we can enumerate each face in turn. Thus we reduce the
problem of enumerating all values on the layer to enumerating each of
the @racket[2]-dimensional faces. For this case, the maximal element
of the tuple is the middle one: we get @racket['(0 3 2)].

@;{ how much glory do we need below?
@racketblock[(define (box-untuple k)
               (λ (n)
                 (define layer (integer-root n k)) ; floor of the kth root of n
                 (define smallest (expt layer k))  ; layer^k
                 (define layer/e (bounded-list/e k layer))
                 (decode layer/e (- n smallest))))]
                 
Here @racket[bounded-list/e] is a function that takes a positive
integer list length @racket[k] and a natural number bound
@racket[layer] and returns an enumeration of lists of length
@racket[k] that have a maximal value of @racket[layer]. For example the values of @racket[(bounded-list/e 3 2)] are

@enum-example[(slice/e (list/e natural/e natural/e natural/e) 8 10000000000) 19]

Since the elements of the enumerated lists are bounded by a specific
number, @racket[bounded-list/e] always returns a finite enumeration,
which we denote @racket[e]. Furthermore, enumerating every element of
@racket[e] will use all of its arguments in exactly the same way since
for any tuple @racket[(i_1 i_2 ... i_k)] in @racket[e], every
permutation of that tuple is also in @racket[e], since it has the same
maximum.
}

As a final optimization, we found that it is faster to prime factorize
the length and then use compose @racket[list/e] calls at smaller
lengths. For instance, to enumerate lists of length @racket[6], we
enumerate pairs of lists of length @racket[3]. Composing the fair
enumerators in this way results in an enumeration that is also fair.

