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

We say an enumeration combinator is unfair if it is not fair.

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

@section{Fair Union}
@;{TODO: write this section..}

Next we turn to @racket[disj-sum/e], the operation corresponding to the
union of several enumerators.
Recall that the arguments for @racket[disj-sum/e] are not just enumerators, but pairs
consisting of an enumerator and a predicate to that returns true if a
value is in that enumerator, in line with the Racket convention of
using untagged union types. We will denote a call to
@racket[disj-sum/e] with @racket[k] arguments by
@racket[(disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?))]
where given that @racket[x] is in one of the @racket[e_i], @racket[(1? x)] is true if there is some index @racket[i] such that @racket[(decode e_1 i)] is @racket[x].

@(define symbol/e (except/e var/e '||))
@racket[disj-sum/e] is relatively easy to define fairly. Given two infinite argument enumerations, we can simply alternate between one and the other, so the first ten elements of @racket[(disj-sum/e (nat/e nat?) (symbol/e sym?))] are simply the first five elements of @racket[nat/e] and @racket[string/e] interleaved, where @racket[symbol/e] is some enumeration of all Racket symbols:
@enum-example[(disj-sum/e (cons nat/e number?)
                          (cons symbol/e symbol?)) 10]

Again, to achieve fairness we cannot simply use the binary version of
@racket[disj-sum/e] arbitrarily. For example, if we defined
@(define (union-three/e ep_1 ep_2 ep_3)
   (define e_2 (car ep_2))
   (define 2?  (cdr ep_2))
   (define e_3 (car ep_3))
   (define 3?  (cdr ep_3))
   (define (2-or-3? x) (or (2? x) (3? x)))
   (disj-sum/e ep_1 (cons (disj-sum/e ep_2 ep_3) 2-or-3?)))
@racketblock[(define (union-three/e ep_1 ep_2 ep_3)
               (define e_2 (car ep_2))
               (define 2?  (cdr ep_2))
               (define e_3 (car ep_3))
               (define 3?  (cdr ep_3))
               (define (2-or-3? x) (or (2? x) (3? x)))
               (disj-sum/e ep_1 (cons (disj-sum/e ep_2 ep_3) 2-or-3?)))]
then enumerating the first 10 elements of               
@racket[(union-three/e (cons nat/e nat?) (cons symbol/e sym?) (cons float/e float?))]
is unfairly weighted to the first argument:
@(centered (disj-sum-pict/bad))

A fair generalization is fairly obvious. First we decode each argument
with the value @racket[0], then each with @racket[1], and so on. So
when given a call
@racket[(decode (disj-sum/e (cons e_1 1?) ... (cons e_k k?)) i)]
we divide @racket[i] by @racket[k], giving us a quotient of @racket[q]
and remainder of @racket[r]. Then we call @racket[(decode e_r q)]. We
see that, like @racket[list/e], we have a notion of "layers", if we
think of the input enumerations as infinitely tall columns side by
side, each layer is a horizontal slice of the columns. So using the same enumerations as before, @racket[(disj-sum/e (cons nat/e exact-integer?) (cons symbol/e sym?) (cons float/e float?))] looks like this:
@(centered (disj-sum-pict/good))
              
Unlike @racket[list/e], @racket[disj-sum/e] enumerator also has an
intuitive notion of fairness for finite enumerations. For example this
enumeration:
@racketblock[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) sym?)
                         (cons nat/e number?)
                         (cons (fin/e "x" "y") string?))]
cycles through its two finite enumeration arguments until they
are exhausted before producing the rest of the natural
numbers:
@enum-example[(disj-sum/e (cons (fin/e 'a 'b 'c 'd) symbol?)
                          (cons nat/e number?)
                          (cons (fin/e "x" "y") string?))
              14]
In general, this means that @racket[disj-sum/e] must track the
ranges of natural numbers when each finite enumeration is exhausted
to compute which enumeration to use for a given index.

@;{TODO: theorem style}

Theorem: @racket[disj-sum/e] is fair

Proof.

We claim that @racket[disj-sum/e] is fair. When called with
@texmath{k} arguments @racket[e_1 e_2 ... e_k] the sequence
@texmath{M_i = k(i+1)} is an infinite increasing sequence for which
when enumerating
@racket[(disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?))]
with all indices greater than or equal to
@texmath{0} and less than @texmath{M_i=k(i+1)} the enumerations
@racket[e_1 e_2 ... e_k] are called with the same arguments,
specifically @texmath{0\cdots i}. We proceed by induction on
@texmath{i}.  For @texmath{i=0}, @texmath{M_0=k} and for
@texmath{j=0\cdots(k-1)}, we have
@racket[(decode (disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?)) j)]
is exactly
@racket[(decode e_{j+1} 0)] so each argument is called with the same
number @texmath{0} exactly once. Then assuming this holds for
@texmath{M_i}, for @texmath{M_{i+1} = k(i+2)} we know by inductive
hypothesis that decoding from @texmath{0} to @texmath{M_i=k(i+1)}
calls all arguments with the same values so we need only show that
decoding from @texmath{M_i=k(i+1)} up to but not including
@texmath{M_{i+1}=k(i+2)} uses all arguments equally, and similarly to
the base case, by the definition of @racket[disj-sum/e],
@racket[(decode (disj-sum/e (cons e_1 1?) (cons e_2 2?) ... (cons e_k k?)) (+ (* k (+ i 1)) j))]
is equal to @racket[(decode e_{j+1} (* k (+ i 1)))] so all arguments
are called with the same value. Thus @racket[disj-sum/e] is fair.

@;{TODO: (disj-sum/e (e_1 1?) ((disj-sum/e (e_2 2?) (e_3 3?)) (or 2? 3?)))}
Theorem: @racket[union-three/e] is unfair.

Proof.
We use the following equivalent definition for the decoding function of @racket[(union-three/e (cons e_1 1?) (cons e_2 2?) (cons e_3 3?))]:
@racketblock[(define (decode-three i)
               (define (q r) (quotient/remainder i 3))
               (match r
                 [1 (decode e_2 (quotient q 2))]
                 [3 (decode e_3 (quotient q 2))]
                 [else (decode e_1 q)]))]
                 
Now we will show that, similarly to the proof that @racket[triple/e]
is unfair, for any @texmath{n > 4} there is an @texmath{i < n} and
@texmath{h} such that
@racket[(decode (union-three/e (cons e_1 1?) (cons e_2 2?) (cons e_3 3?)) i)]
is equal to @racket[(decode e_1 h)] but there is no
@texmath{j} such that
@racket[(decode (union-three/e (cons e_1 1?) (cons e_2 2?) (cons e_3 3?)) j)]
is @racket[(decode e_2 h)]. In other
words, for any @texmath{n > 4}, when enumerating all values of
@racket[(union-three/e (cons e_1 1?) (cons e_2 2?) (cons e_3 3?))]
from @racket[0] to @racket[n], @racket[e_1] has been called with an
index with which @racket[e_2] has not been called.

This relies on two basic properties of @racket[decode-three]. First,
that when enumerating all indices @racket[0] to @racket[n],
@racket[e_1] has been called with the index @texmath{\lfloor n/2\rfloor}.
Second, that when enumerating all indices @racket[0] to
@racket[n], @racket[e_2] has been called with indices that are all
less than or equal to @texmath{\lfloor(\lfloor n/2\rfloor)/2\rfloor}.
Both of these properties are direct from the
definition of @racket[decode-three]. Then, we note that for @texmath{n>4},
@texmath{n - (\lfloor n/2\rfloor) > 2} so for @texmath{n>4}, @texmath{\lfloor(\lfloor n/2\rfloor)/2\rfloor < \lfloor n/2\rfloor} so the largest value indexed into @racket[e_1] has not been used to index into @racket[e_2]. Thus @racket[decode-three] is unfair.

