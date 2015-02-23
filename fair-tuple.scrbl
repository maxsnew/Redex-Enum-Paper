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

For enumerations we are primarily concerned with the other
half of the bijection, since that is the one used to generate
terms. For the pairing case, these functions have fairly
straightforward inverses, but their generalizations do not. This is
the generalization of the cantor pairing function to length
@raw-latex{$k$} tuples:
@centered{@raw-latex{$cantor\_tuple(n_1,n_2,\ldots,n_k) =
{{k-1+n_1+\cdots+n_k}\choose{n}}+\cdots+{{1+n_1+n_2}\choose{2}} +
{{n_1}\choose{1}}$}} This means to be able to invert such equations is
to solve a certain class of arbitrary degree diophantine
equations, which are not generally solvable. We
can easily define a highly inefficient (but correct) way to compute
the inverse by trying every natural number, in order, applying the
original @raw-latex{$cantor\_tuple$} function to see if it was the
argument given. @citet[inverting-cantor-n-tupling] improves on
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

The key idea is that we find what “layer” a value is on and we
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

Now, let @racket[cantor-list/e] be a version of @racket[list/e] be a
that uses the generalized Cantor @texmath{n}-tupling bijection
described above. This is highly analogous to the boxy
@racket[list/e]. For example, their @racket[args] functions both
return lists of length 1 in every slot and their @racket[build]
functions are exactly the same. To be precise @racket[(args i)] is
equal to @racket[((i_1) (i_2) ... (i_k))] where
@raw-latex{\[i = \binom{i_1}{1} + \binom{1+i_1+i_2}{2}+\cdots+\binom{k-1+i_1+\cdots+i_k}{k}\]}
which the last equation is exactly generalized Cantor @texmath{k}-tupling.

@theorem{@racket[cantor-list/e] is fair}

@proof{
We elide most details of the proof since it is almost exactly the same
as the proof for boxy @racket[list/e]. First, we note that as
described in @citet[cantor-n-tupling], the Cantor tupling bijection
works in a similar way to the boxy bijection, that is, for @texmath{k}
inputs it traces out the outer face of increasingly large
@texmath{k}-simplices. This means it can be computed by taking a
"root" of the input index and then using the remainder to index into a
finite enumeration. In particular for @texmath{k} inputs, it takes the
@texmath{k}-th simplicial root giving a root of @texmath{l} and
remainder @texmath{r} then uses @texmath{r} to index into an
enumeration of all lists of length @texmath{k} whose elements sum to
@texmath{l}. And as with @racket[bounded-list/e], an enumeration of
lists of length @texmath{k} that sum to the value @texmath{l}, when
fully enumerated, calls the arguments @racket[e_i] with the same
values. Thus we can show that there is an infinite increasing sequence
@texmath{(M_0,M_1,...)} where indexing @texmath{0} to @texmath{M_i}
uses all @racket[e_i] equally. For @texmath{k} arguments,
@texmath{M_i = \binom{i+k-1}{k}}, the @texmath{i}th
@texmath{k}-simplicial number. The proof is then precisely analagous
to the proof for boxy @racket[list/e].
@qed
}

Now recall @racket[triple/e], as defined at the beginning of this
section. Let @texmath{args_{cons}} be the args function for
@texmath{cons/e}, which uses the boxy bijection on pairs. Then the
@texmath{args} function for @racket[triple/e] is
@texmath{args(i) = ([i_1], [i_2], [i_3])}
where @texmath{([i_1], [j]) = args_{cons}(i)} and
@texmath{(i_2,i_3) = args_{cons}(j)}. The build function for
@racket[triple/e] is
@racket[(define (build is_1 is_2 is_3) (cons (first is_1) (cons (first is_2) (first is_3))))].

@theorem{@racket[triple/e] is unfair}

@proof{

To prove something is unfair we must show that there is a natural
number @texmath{M} such that for every @texmath{m > M}, there are
indices @texmath{h,j\in\{1,2,3\}} such that @texmath{L_h} and
@texmath{L_j} are not equivalent. To show that two lists are not
equivalent it is sufficient to show that there is a value in one that
is not in the other. Specifically we will show that for all natural
numbers greater than @texmath{4}, @texmath{L_1} contains an index
greater than any found in @texmath{L_2}.

First we establish some elementary properties of @texmath{args_cons},
defined using the boxy bijection on 2 enumerations. First, for any
natural number @texmath{i}, if @texmath{args(i) = ([i_1], [i_2])} then 
@texmath{i_1,i_2 \le \lfloor\sqrt{i}\rfloor}. This is a direct consequence of the
definition of the boxy bijection, which is defined by taking the floor
of the square root of @texmath{i} and then producing a pair whose max
is @texmath{\lfloor\sqrt{i}\rfloor}. Next, for any positive natural number
@texmath{i}, there is a natural number @texmath{l} such that
@texmath{\lfloor\sqrt l\rfloor = \lfloor\sqrt i\rfloor - 1} and
@texmath{args(l) = ([\lfloor\sqrt l\rfloor], [0], [0])}.

First there is a natural number @texmath{l} with
@texmath{\lfloor\sqrt l\rfloor = \lfloor\sqrt i\rfloor - 1}
for any @texmath{i > 0}.
Then the rest of the statement is true by the definition of the boxy
bijection since at least one of the lists in the triple
@texmath{args(i)} must be @texmath{\lfloor\sqrt i\rfloor} since it is
selected from @racket[(bounded-list/e 3 (floor (sqrt i)))], so the
values in @racket[(bounded-list/e 3 (floor (sqrt l)))] must have all
been enumerated before @racket[i] since
@texmath{\lfloor\sqrt l\rfloor < \lfloor\sqrt i\rfloor}.

Thus for any natural number @texmath{i > 9}, if @texmath{L_1,L_2} are
the elements from the first and second column when applying
@texmath{args} to the values @texmath{0} to @texmath{i-1}, we get that
@texmath{L_1} contains some @texmath{l} such that
@texmath{\lfloor\sqrt l\rfloor = \lfloor\sqrt i\rfloor - 1} by our
second lemma. On the other hand, since the values in @texmath{L_2} go
through two calls to @texmath{args_{cons}}, for any
@texmath{x\in L_2},
@texmath{x \le \lfloor\sqrt{\lfloor\sqrt{i}\rfloor}\rfloor}.
So we need to prove that
@texmath{\lfloor\sqrt i\rfloor - 1 > \lfloor\sqrt{\lfloor\sqrt{i}\rfloor}\rfloor}
which is true for all@texmath{i > 9}, so @texmath{L_1} contains a
value larger than any in @texmath{L_2}, so @texmath{L_1} and
@texmath{L_2} are not equivalent. Thus @racket[triple/e] is unfair.
@qed
}
@;{TODO: prime factorized list/e is fair?} 

