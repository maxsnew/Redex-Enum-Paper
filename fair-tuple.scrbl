#lang scribble/lncs

@(require pict
          scribble/manual
          racket/draw
          redex/private/enumerator
          plot
          scriblib/figure
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title{Fair Tupling}
@;{TODO: talk about finite vs infinite}

The combinatorically-inclined reader may have noticed in our
description of @racket[cons/e] that we did not use the classic Cantor
pairing function for our bijection, which can be interpreted as a more
triangular grid walk:@centered{@cantor-cons-pict[]}

Instead we use @citet[elegant-pairing-function]'s bijection,
that we refer to as ``boxy'' pairing. The two bijections are quite similar, they are both quadratic
functions with similar geometric interpretations: boxy traces out the
edges of increasingly large squares and Cantor traces out the bottoms
of increasingly large triangles. This point of view leads to obvious
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

@;{Hilbert's 10th problem reference really necessary?}

whereas for enumerations we are primarily concerned with the other
half of the bijection, since that is the one used to generate
terms. For the pairing case, these functions have fairly
straightforward inverses, but their generalizations do not. This is
the generalization of the cantor pairing function to length
@raw-latex{$k$} tuples:
@centered{@raw-latex{$cantor\_tuple(n_1,n_2,\ldots,n_k) =
{{k-1+n_1+\cdots+n_k}\choose{n}}+\cdots+{{1+n_1+n_2}\choose{2}} +
{{n_1}\choose{1}}$}} This means to be able to invert such equations is
to solve a certain class of arbitrary degree diophantine
equations. While the solution to Hilbert's $10\textsuperscript{th}$
problem is that Diophantine equations are not generally solvable, we
can easily define a highly inefficient (but correct) way to compute
the inverse by trying every natural number, in order, applying the
original @raw-latex{$cantor\_tuple$} function to see if it was the
argument given. In @citet[inverting-cantor-n-tupling], they improve on
this implementation, but the algorithm there is still a search
procedure, and we found it too slow to use in practice.

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

The key takeaway is that we find what "layer" a value is on and we
bootstrap the implementation with existing implementations of
@racket[cons/e] and @racket[disj-sum/e] for finite enumerations,
giving us both halves of the layer enumeration in one fell
swoop. Fortunately, unlike the Cantor pairing function, this is
naturally generalized to an @raw-latex{$n$}-tupling function, by using
the @raw-latex{$n$}th root and @raw-latex{$n$}th power intead of the
square root and squaring. Otherwise the description is the same.

@;{TODO: boxy-list/e is fair}
@;{TODO: reference the racket source code for bounded-list/e}

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

@enum-example[(slice/e (list/e nat/e nat/e nat/e) 8 10000000000) 19]

Since the elements of the enumerated lists are bounded by a specific
number, @racket[bounded-list/e] always returns a finite enumeration,
which we denote @racket[e]. Furthermore, enumerating every element of
@racket[e] will use all of its arguments in exactly the same way since
for any tuple @racket[(i_1 i_2 ... i_k)] in @racket[e], every
permutation of that tuple is also in @racket[e], since it has the same
maximum.

@;{TODO: add theorem styling}
Theorem: @racket[list/e] is a fair combinator

Proof.
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
that is @texmath{M_i = (i+1)^k}. We proceed by induction on
@texmath{i}. For @texmath{i=0}, @texmath{M_0=1}, so we need only
consider the value @racket[(decode (list/e e_1 e_2 ... e_k) 0)] which
is exactly @racket[(list (decode e_1 0) (decode e_2 0) ... (decode e_k 0))],
which calls all argument enumerations with the value @racket[0] and
only @racket[0]. Next, assuming the theorem holds for all
@texmath{M_i} with @texmath{i<l} we seek to prove it holds for
@texmath{M_l}. We know the @racket[e_i] are called with the same
arguments for the indices greater than or equal to @texmath{0} and
less than @texmath{M_{l-1} = l^k} so we need only to show that the
@racket[e_i] are called with the same arguments for indices greater
than or equal to @texmath{l^k} and less than @texmath{(l+1)^k}. Those
indices @texmath{j} are precisely the natural numbers for which
@texmath{\lfloor\sqrt[k]{j}\rfloor = l} and thus together they fully
enumerate the values of @racket[(bounded-list/e k l)], thus by our
lemma, when called with those indices, the arguments @racket[e_i] are
indexed with all the same indices. Thus indexing from @texmath{0} to @texmath{M_l} uses all @racket[e_i] equally, so by induction, @racket[list/e] is fair.

Now, let @racket[cantor-list/e] be a version of @racket[list/e] be a
that uses the generalized Cantor
@texmath{n}-tupling bijection described above.

@;{TODO: theorem style}
Theorem: @racket[cantor-list/e] is fair

Proof.

We elide most details of the proof
since it is almost exactly the same as the proof for boxy
@racket[list/e]. First, we note that as described in
@citet[cantor-n-tupling], the Cantor tupling bijection works in a
similar way to the boxy bijection, that is, for @texmath{k} inputs it
traces out the outer face of increasingly large
@texmath{k}-simplices. This means it can be computed by taking a
"root" of the input index and then using the remainder to index into a
finite enumeration. In particular for @texmath{k} inputs, it takes the
@texmath{k}-th simplicial root giving a root of @texmath{l} and
remainder @texmath{r} then uses @texmath{r} to index into an enumeration of
all lists of length @texmath{k} whose elements sum to @texmath{l}. And
as with @racket[bounded-list/e], an enumeration of lists of length @texmath{k} that sum to the value @texmath{l}, when fully enumerated, calls the arguments
@racket[e_i] with the same values. Thus we can show that there is an
infinite increasing sequence @texmath{(M_0,M_1,...)} where indexing
@texmath{0} to @texmath{M_i} uses all @racket[e_i] equally. For
@texmath{k} arguments, @texmath{M_i = \binom{i+k-1}{k}}, the
@texmath{i}th @texmath{k}-simplicial number. The proof is then
precisely analagous to the proof for boxy @racket[list/e].

Now recall @racket[triple/e], as defined at the beginning of
this section.

@;{TODO: Theorem style}
Theorem: @racket[triple/e] is unfair

Proof.

To do this we must show that there is a
natural number @texmath{M} such that for every @texmath{m > M}, the
multiset of calls to the argument enumerations @racket[e_i] are
different. Specifically we will show that for all natural numbers
greater than @texmath{4}, the multiset of calls to the first argument
@racket[e_1] contains an index greater than any found in the multisets
for @racket[e_2] and @racket[e_3].

@;{TODO: slightly cleaner proof using floor(sqrt(floor(sqrt(i)))) < floor(sqrt(i-1)) for i > 4}
First we establish some elementary properties of @racket[cons/e],
defined using the boxy bijection on 2 enumerations. First, for any
natural number @texmath{i}, there exist @texmath{i_1}, @texmath{i_2}
such that @racket[(decode (cons/e e_1 e_2) i)] is equal to
@racket[(cons (decode e_1 i_1) (decode e_2 i_2))] and
@texmath{i_1,i_2 \le \lfloor\sqrt{i}\rfloor}. This is a direct consequence of the
definition of the boxy bijection, which is defined by taking the floor
of the square root of @texmath{i} and then producing a pair whose max
is @texmath{\lfloor\sqrt{i}\rfloor}. Next, for any natural number
@texmath{i}, @racket[(decode (triple/e e_1 e_2 e_3) (* i i))] is equal
to @racket[(cons (decode e_1 i) (cons (decode e_2 0) (decode e_3
0)))], This is a direct usage of the definition, assuming the
enumeration produced by @racket[bounded-list/e] produces this value
first (as our implementation does). Thus for any natural number
@texmath{i}, enumerating all values from @texmath{0} to @texmath{i},
@racket[e_1] has been called with @texmath{\lfloor\sqrt{i}\rfloor}
while for any @texmath{j} with which @racket[e_2] and @racket[e_3]
have been called, @texmath{j \le \lfloor\sqrt{\lfloor\sqrt{i}\rfloor}\rfloor}.
Then we note that if
@texmath{i > 4}, then @texmath{\lfloor\sqrt{i}\rfloor < i}, so
@texmath{\lfloor\sqrt{\lfloor\sqrt{i}\rfloor} < \lfloor\sqrt{i}\rfloor} and thus @racket[e_1] has been called with a
value greater than any value @racket[e_2] or @racket[e_3] have been
called with and thus @racket[triple/e] is unfair.

@;{TODO: prime factorized list/e is fair?} 

