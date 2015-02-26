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

@title{Fair Pairing}

For pairing we use @citet[elegant-pairing-function]'s bijection, that we
refer to as ``boxy'' pairing, which is specified in the "cons/e x" and
"cons/e y" rules in @Figure-ref["fig:semantics"].

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
For the full details of the proof of the theorem, see the coq
development. The theorem is called @racket[Pair_Fair] and it appears
in section @racket[PairFair].

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

The theorem is called @racket[NaiveTripleUnfair] in the coq model and
it appears in section @racket[NaiveTripleUnfair].

@;{
@;{TODO: move all of this to the previous section}
The two bijections
are quite similar; they are both quadratic functions with similar
geometric interpretations: boxy traces out the edges of increasingly
large squares and Cantor traces out the bottoms of increasingly large
triangles.



The combinatorially-inclined reader may have noticed in our
description of @racket[cons/e] that we did not use the classic Cantor
pairing function for our bijection, which can be interpreted as a more
triangular grid walk:@centered{@cantor-cons-pict[]}

Similarly, a version of @racket[cons/e] that uses
the Cantor pairing function would also be fair. The equilibria are then the
triangle numbers, rather than the perfect squares.

The geometric point of view leads to obvious
generalizations to n-tuples. Generalized boxy should trace out the
outer faces of an n cube and generalized Cantor should trace out the
outer face of an n simplex.

Despite their conceptual similarity, we found the boxy enumeration
lends itself to a more efficient implementation. To understand why, note
that most combinatorics applications of pairing functions are chiefly
concerned with one half of the bijection: the one from pairs of
natural numbers to natural numbers.
@centered{@raw-latex{$cantor\_pair(m, n) = \frac{(n+m)(n+m+1)}{2} + m$}}
@centered{@raw-latex{$box\_pair(m, n) = \begin{cases} x^2+x+y &\mbox{if } x\ge y\\ x+y^2   &\mbox{if } x < y \end{cases}$}}

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
compute an efficient inverse? A geometric interpretation gives the
answer. If we look back at the grid-walk describing @racket[cons/e] a
pattern emerges, as the input indices grow, we trace out increasingly
large squares. For example, when we encode @racket[42] with
@racket[cons/e], we first take the square root with remainder, giving
us a root of @racket[6] with a remainder of @racket[8]. This tells us
that the larger value in the pair is @racket[6], and it's the
@racket[8]th such pair. Then we construct an enumeration of pairs
whose larger value is @racket[6], and index into that enumeration with
@racket[8], giving us the pair @racket['(6 . 0)]. Then we can easily
get the inverse transform by taking that pair, taking the maximum of
@racket[6] and @racket[0] to get @racket[6], and then we use the other
half of the enumeration of pairs above to find where in the
enumeration of pairs with larger value @racket[6] this @racket['(6
. 0)] is, and we find it is the @racket[8]th such pair. Then we square
@racket[6] to get @racket[36] and finally add @racket[8] to get our
original value of @racket[42].

The key idea is that we find what ``layer'' a value is on and we
bootstrap the implementation with existing implementations of
@racket[cons/e] and @racket[disj-sum/e] for finite enumerations,
giving us both halves of the layer enumeration in one fell
swoop. Fortunately, unlike the Cantor pairing function, this is
naturally generalized to an @raw-latex{$n$}-tupling function, by using
the @raw-latex{$n$}th root and @raw-latex{$n$}th power intead of the
square root and squaring. Otherwise the description is the same.

We now prove that @racket[list/e], using the generalized boxy
bijection, is fair. The following is a function that takes a positive
number @racket[k] and returns the decoding function the boxy bijection for @racket[k]-tuples specialized to natural numbers:

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

In order to show that @racket[list/e] is fair as we've defined it, we
must define its @racket[args] and @racket[build]
functions. @racket[args] is defined using the process above, which
given an @racket[i] produces a list @racket[(i_1 ... i_k)] of indices
with max @texmath{\lfloor i^{1/k}\rfloor} but to satisfy the type of
@racket[args], it wraps each of those indices in a list to return
@racket[((i_1)) ... ((i_k))], meaning that the enumeration produced by
@racket[list/e] uses each of its argument enumerations once per
decode. @racket[build] is defined as @racket[(define (build xs) (map first xs))],
and it is linear since each of its arguments will only
have one element in them since they were produced by the @racket[args]
function.

@theorem{@racket[list/e] is a fair combinator}

@proof{
With this lemma in hand, we prove that @racket[list/e] is fair by
showing that for any infinite argument enumerations @racket[(e_1 e_2 ... e_k)]
there is an infinite increasing sequence
@texmath{(M_0,M_1,...)} of natural numbers such that for any
@texmath{M_i} in the sequence, enumerating with all indices less than
@texmath{M_i} in @racket[(list/e e_1 e_2 ... e_k)] calls all arguments
@racket[e_j] with the same indices. This is sufficient to show that
@racket[list/e] is fair since for any natural number @texmath{m} there
is some @texmath{M_i > m} since @texmath{(M_0,M_1,...)} is infinite
and increasing.

Specifically, our sequence is the sequence of @texmath{k}th powers,
that is @texmath{M_i = (i+1)^k}. Let
@texmath{h_1,h_2\in\{1,\ldots,k\}}, representing two arbitrary argument
enumerations. We proceed by induction on @texmath{i}. For
@texmath{i=0}, @texmath{M_0=1}, so we need only consider the call
@racket[(args 0)] which results in @racket[((0) ... (0))] so
@texmath{L_{h_1}=L_{h_2}=[0]} i.e., both argument enumerations are
used with the value @racket[0] and only @racket[0]. Next, assuming the
theorem holds for all @texmath{M_i} with @texmath{i<l} we seek to
prove it holds for @texmath{M_l}.

If @texmath{L_{h_1}',L_{h_2}'} are the lists of @texmath{h_1,h_2}
values resulting from calls to args for @texmath{0} up to
@texmath{M_{l-1} - 1 = l^k - 1}, then by inductive hypothesis
@texmath{L_{h_1}',L_{h_2}'} are permutations of each other. Then if we
can show that the lists of @texmath{h_1,h_2} values from calls to args
for @texmath{M_{l-1}=l^k} to @texmath{M_l-1=(l+1)^k-1} are
permutations of each other, then we know that the @texmath{h_1,h_2}
calls from @texmath{0} to @texmath{M_l-1} will be permutations of each
other. Those indices @texmath{j} are precisely the natural numbers for
which @texmath{\lfloor\sqrt[k]{j}\rfloor = l} and thus together they
fully enumerate the values of @racket[(bounded-list/e k l)], thus by
our lemma, when called with those indices, the @texmath{h_1,h_2}
indices will be the same. Thus indexing from @texmath{0} to
@texmath{M_l} uses all @racket[e_i] equally, so by induction,
@racket[list/e] is fair.
@qed
}

@;{TODO: prime factorized list/e is fair?} 

}

