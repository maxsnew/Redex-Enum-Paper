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

@title[#:tag "sec:fair"]{Combinator Fairness}

A fair enumeration combinator is one that indexes into its
given enumerators roughly equally, instead of indexing
deeply into one and shallowly into a different one. For
example, imagine we waned to build an enumerator for lists
of length 4. This enumerator is one way to build it:
@racketblock[(cons/e
              nat/e
              (cons/e
               nat/e
               (cons/e
                nat/e
                (cons/e
                 nat/e
                 (fin/e null)))))]
Unfortunately, it is not fair. This is the 1,000,000,000th element,
@code{@(format "~v"
             (decode (cons/e
                      nat/e
                      (cons/e
                       nat/e
                       (cons/e
                        nat/e
                        (cons/e
                         nat/e
                         (fin/e null)))))
                     1000000000))}
and, as you can see, it has indexed far more deeply into the first
@racket[nat/e] than the others. In contrast, if we balance the @racket[cons/e]
expressions differently and use a @racket[map/e] to build the actual list:
@racketblock[(map/e
              (λ (x) (list (caar x) (cadr x) (cdar x) (cddr x)))
              (λ (l) (cons (cons (list-ref l 0) (list-ref l 1))
                           (cons (list-ref l 4) (list-ref l 3))))
              (cons/e
               (cons/e nat/e nat/e)
               (cons/e nat/e nat/e)))]
then the billionth element is
@code{@(format "~v"
             (decode 
              (map/e
               (λ (x) (list (caar x) (cadr x) (cdar x) (cddr x)))
               (λ (l) (cons (cons (list-ref l 0) (list-ref l 1))
                            (cons (list-ref l 4) (list-ref l 3))))
               (cons/e
                (cons/e nat/e nat/e)
                (cons/e nat/e nat/e)))
              1000000000))}, 
which is much more balanced. This balance isn't specific to
just that index in the enumeration, either. @Figure-ref["fig:unfairness"]
shows histograms for each of the components when using an
the unfair @racket[(cons/e nat/e (cons/e nat/e nat/e))]
and when using a fair tupling that combines three @racket[nat/e] 
enumerators. The x-coordinates of the plot correspond to the different
values that appear in the tuples and the height of each bar is
the number of times that particular number appeared when enumerating
the first 1,000 tuples. As you can see, all three components have the
same set of values for the fair tupling operation, but the first tuple
element is considerably different from the other two when using the
unfair combination.

@figure*["fig:unfairness"
         @list{Histograms of the occurrences of each natural number
               in fair and unfair tuples}
         (parameterize ([plot-width 135]
                        [plot-height 135])
           (unfairness-histograms))]

Fair combinators give us predictability for programs that
use our enumerators. In Redex, our main application of
enumeration combinators, fairness ensures that when a Redex
programmer may makes an innocuous change to the grammar of
the language (e.g. changing the relative order of two
subexpressions in expression form) then the enumeration
quality is not significantly affected. For example, consider
an application expression. From the perspective of the
enumerator, an application expression looks just like a list
of expressions. An unfair enumerator might cause our
bug-finding search to spend a lot of time generating
different argument expressions and always using similar
(simple, boring) function expressions. 

Of course, the flip-side of this coin is that using unfair
combinators can also improve the quality of the search in
some cases, even over fair enumeration. For example, when we
are enumerating expressions that consist of a choice between
variables and other kinds of expressions, we do not want to
spend lots of time trying out different variables because most
models are sensitive only to when variables differ from 
each other, not their exact spelling. Accordingly unfairly
biasing our enumerators away from different variables 
can be win for finding bugs. Overall, however, it is important
that we do have a fair set of combinators that correspond
to the way that Redex programs are constructed and then when
Redex programs are compiled into the combinators, the compilation
can use domain knowledge about Redex patterns to selectively
choose targeted unfairness, but still use fair combinators when it
has no special knowledge.

@section{A Formal Definition of Fairness}

For this section we consider only infinite enumerations, since our
notion of fairness necessitates indexing enumerations with arbitrarily
large natural numbers.

We define an enumeration combinator to be a function whose arguments
are enumerators and output is an enumerator.

We say that an enumeration combinator @racket[c/e] is fair if, for
every natural number @raw-latex{$m$}, there exists a natural number
@raw-latex{$M > m$} and a multiset of natural numbers @raw-latex{S}
such that when calling @racket[(decode (c/e e_1 e_2 ... e_k) i)] with
every value of @raw-latex{$i$} greater than or equal to
@raw-latex{$0$} and less than @raw-latex{$M$}, every argument
enumeration was called with exactly the natural numbers in
@raw-latex{S}.

The definition requires some unpacking. First, the fact that every
argument was called with the same multiset of indices is saying that
when enumerating all values from @raw-latex{$0$} to @raw-latex{$M$},
every argument enumeration is called with the same inputs, the same
number of times. The usage of the value @raw-latex{$M$} in the
definition allows combinators to favor certain argument enumerations
for one value or several as long as fairness is again established
after some finite number of steps. For instance @racket[disj-sum/e]
has to use one of its arguments first, so it can't be fair "at every
point", but when called with @raw-latex{$k$} arguments, it
re-establishes fairness every @raw-latex{$k$} indices.

As a concrete example, consider the @racket[cons/e] operator as
described earlier, but limited to only take 2 argument
enumerations. Then given any natural number @raw-latex{$m$}, we define
@raw-latex{$M = (m+1)^2$}, and then when enumerating all values of
@racket[(cons/e e_1 e_2)] less than @racket[M], we call each argument
with every value between @raw-latex{$0$} and @raw-latex{$m$},
@raw-latex{$m$} times. Instantiating @raw-latex{$m$} with @texmath{6},
we see that for the indices @math{0} to @math{6}, we've used one side
of the enumeration (the @texmath{y}-axis here) with slightly larger
values than the other:

@(centered (grid cons/e 5 6 200 12))

But if we look at all the values up to @texmath{49=(6+1)^2} then we've
both enumerations in the same way, making our walk here symmetric
along the diagonal:

@(centered (grid cons/e 7 48 200 12))

As a non-example, we abstract our earlier example of an unfair
combinator to define a tripling combinator:

@racketblock[(define (triple/e e_1 e_2 e_3)
               (cons/e e_1 (cons/e e_2 e_3)))]

To see that this is not fair, we look at the first 21 values of
@racket[(cons/e nat/e (cons/e nat/e nat/e))]:

@enum-example[(cons/e nat/e (cons/e nat/e nat/e)) 21]

and we see that the first argument enumeration has been called with
@racket[3] before the other arguments have been called with @racket[2]
and the first argument is called with @racket[4] before the others are
called with @racket[3] this behavior persists for all input indices,
so that no matter what natural number we choose greater than or equal
to @racket[7], the first argument enumerator will have been called
with a value larger than any the other two arguments have been called
with. Thus, @racket[triple/e] is unfair.

@section{Fair Tupling}
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

@;{TODO: triple/e is unfair}
@;{TODO: cantor-list/e is fair}
@;{TODO: prime factorized list/e is fair?} 

@section{Fair Union}
@;{TODO: write this section..}
The @racket{disj-sum/e}'s ...
The @racket[disj-sum/e] enumerator also has to be fair and
to account for finite enumerations. So this
enumeration:
@racketblock[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                         (cons nat/e number?)
                         (cons (fin/e "x" "y") string?))]
has to cycle through the finite enumerations until they
are exhausted before producing the rest of the natural
numbers:
@enum-example[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                          (cons nat/e number?)
                          (cons (fin/e "x" "y") string?))
              14]
In general, this means that @racket[disj-sum/e] must track the
ranges of natural numbers when each finite enumeration is exhausted
to compute which enumeration to use for a given index.

@;{TODO: disj-sum/e is fair}
@;{TODO: (disj-sum/e (e_1 1?) ((disj-sum/e (e_2 2?) (e_3 3?)) (or 2? 3?)))}
