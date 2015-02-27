#lang scribble/sigplan

@(require pict
          scribble/manual
          racket/draw
          racket/list
          racket/contract
          data/enumerate/lib
          plot
          scriblib/figure
          redex/pict
          "model/model.rkt"
          "unfairness-hist.rkt"
          "cite.rkt"
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair-informal"]{Fairness}

@(define one-billion 1000000000)
@(define fair-number-past-one-billion (* 1000 one-billion))
@(unless (integer? (sqrt (sqrt fair-number-past-one-billion)))
   (error 'ack! "not fair!"))
@(define fair-four-tuple 
   (map/e
    (λ (x) (list (caar x) (cdar x) (cadr x) (cddr x)))
    (λ (l) (cons (cons (list-ref l 0) (list-ref l 1))
                 (cons (list-ref l 2) (list-ref l 3))))
    (cons/e
     (cons/e natural/e natural/e)
     (cons/e natural/e natural/e))
    #:contract (list/c exact-nonnegative-integer? exact-nonnegative-integer?
                       exact-nonnegative-integer? exact-nonnegative-integer?)))

A fair enumeration combinator is one that indexes into its
argument enumerators roughly equally, instead of indexing
deeply into one and shallowly into another one. For
example, imagine we wanted to build an enumerator for lists
of length 4. This enumerator is one way to build it:
@racketblock[(cons/e natural/e (cons/e natural/e 
              (cons/e natural/e (cons/e natural/e 
               (fin/e null)))))]
The @(add-commas one-billion)th element is
@code{@(format "~v"
               (from-nat (cons/e
                          natural/e
                          (cons/e
                           natural/e
                           (cons/e
                            natural/e
                            (cons/e
                             natural/e
                             (fin/e null)))))
                         one-billion))}
and, as you can see, it has unfairly indexed far more deeply into the first
@racket[natural/e] than the others. In contrast, if we balance the @racket[cons/e]
expressions like this:
@racketblock[(cons/e
              (cons/e natural/e natural/e)
              (cons/e natural/e natural/e))]
(and then use @racket[map/e] to adjust the elements of
the enumeration to actually be lists), then the
@(add-commas one-billion) element is
@code{@(format "~v" (from-nat fair-four-tuple one-billion))},
which is much more balanced. This balance is not specific to
just that index in the enumeration, either. @Figure-ref["fig:unfairness"]
shows histograms for each of the components when using
the unfair @racket[(cons/e natural/e (cons/e natural/e natural/e))]
and when using a fair tupling that combines three @racket[natural/e] 
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

The subtle point about fairness is that we cannot restrict 
the combinators to work completely in lock-step on their argument
enumerations, or else we would not admit @emph{any} pairing operation
as fair. After all, a combinator that builds the pair
of @racket[natural/e] with itself we must eventually produce the pair
@racket['(1 . 4)], and that pair must come either before or
after the pair @racket['(4 . 1)]. So if we insist that at
every point in the enumeration that the combinator's result enumeration
has used all of its argument enumerations equally, then pairing would
be impossible, as would many other combinators.

Instead, we insist that there are infinitely many places in
the enumeration where the combinators reach an equilibrium. That is,
there are infinitely many points where the result of the combinator
has used all of the argument enumerations equally.

As an example, consider the fair nested @racket[cons/e]
from the beginning of the section. As we saw, at the point @(add-commas one-billion),
it was not at equilibrium. But at @(add-commas (- fair-number-past-one-billion 1)),
it produces 
@code{@(format "~v" (from-nat fair-four-tuple (- fair-number-past-one-billion 1)))},
and indeed it has indexed into each of the four @racket[natural/e] enumerations
with each of the first @(add-commas (sqrt (sqrt fair-number-past-one-billion))) natural numbers.

In general, that fair four-tuple reaches an equilibrium point at every
@texmath{n^4} and @racket[(cons/e natural/e natural/e)]
reaches an equilibrium point at every perfect square. The
diagonal in the square diagram from @secref["sec:enum"] illustrates
the first few equilibrium points for @racket[(cons natural/e natural/e)].

As an example of an unfair combinator consider
@racket[triple/e]:
@racketblock[(define (triple/e e_1 e_2 e_3)
               (cons/e e_1 (cons/e e_2 e_3)))]
and the first 25 elements of its enumeration:
@enum-example[(cons/e natural/e (cons/e natural/e natural/e)) 24]
The first argument enumeration has been called with
@racket[3] before the other arguments have been called with @racket[2]
and the first argument is called with @racket[4] before the others are
called with @racket[3] this behavior persists for all input indices,
so that no matter how far we go into the enumeration, there will never
be an equilibrium point after @racket['(0 0 . 0)].

The combinatorially-inclined reader may have noticed in our
description of @racket[cons/e] that we did not use the classic Cantor
pairing function for our bijection, which can be interpreted as a more
triangular grid walk:@centered{@cantor-cons-pict[]}. Instead we use
@citet[elegant-pairing-function]'s bijection, that we refer to as
``boxy'' pairing. The pairing functions are given by

@centered{@raw-latex{$cantor\_pair(m, n) = \frac{(n+m)(n+m+1)}{2} + m$}}
@centered{@raw-latex{$box\_pair(m, n) =
                     \begin{cases} 
                     x^2+x+y &\mbox{if } x\ge y\\
                     x+y^2   &\mbox{if } x < y 
                     \end{cases}$}}

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
@racket[k] that have a maximal value of @racket[layer]. 
For example the values of @racket[(bounded-list/e 3 2)] are

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



============================================================


@section{Union}
@(define either-index 77)
@(define quot (quotient either-index 2))
@(define remainder (modulo either-index 2))
@(define choice/e (if (remainder . = . 0) natural/e string/e))
@(define value  (from-nat choice/e quot))

@;TODO: make the numbers look the same

Our union combinator, @racket[or/e], when viewed as a binary operation
alternates between its 2 arguments. First, it enumerates its arguments
at @racket[0], then @racket[1], etc. To index into @racket[(or/e natural/e string/e)]
at @(add-commas either-index) (where @racket[string/e] is an
enumeration of strings), we just divide by @racket[2] to get
@(add-commas quot) with a remainder of @(add-commas remainder). The
@(add-commas remainder) tells us to index into the @racket[string/e]
enumeration with index @(add-commas quot), giving us @value .

To go the other way, use the contracts on the enumerations to
determine which enumeration a value came from. In which case, we have
a string so we know it came from @racket[string/e]. Then unindex that
value to get its index @(add-commas quot), then multiply that by
@racket[2] and add @racket[1] since it came from @racket[string/e] to
get the original value of @(add-commas either-index).

The typical way to extend to an @texmath{n}-ary combinator would be to
map to nested calls of the binary combinator. Consider a trinary
version implemented this way:

@(define (or-three/e e_1 e_2 e_3)
   (or/e e_1 (or/e e_2 e_3)))
@racketblock[(define (or-three/e e_1 e_2 e_3)
               (or/e e_1 (or/e e_2 e_3)))]

then enumerating some of the first elements of               
@racket[(or-three/e (cons natural/e nat?) (cons symbol/e sym?) (cons float/e float?))]
indicates it is unfairly weighted to the first argument, 
as shown on the left in @figure-ref["fig:disj-sum"].

@figure["fig:disj-sum" "Unfair (left) and fair (right) disjoint union enumerations"]{
@centered{@(hc-append 60 (disj-sum-pict/bad) (disj-sum-pict/good))}
}

For @racket[k] enumeration arguments, the algorithm is very
similar. Just divide the index by @racket[k] and use the remainder to
determine which argument enumeration to use.

Finally, with finite arguments @racket[or/e] approximates the infinite
behavior until an argument is exhausted:

@racketblock[(or/e (fin/e 'a 'b 'c 'd)
                   natural/e
                   (fin/e "x" "y"))]
@enum-example[(or/e (fin/e 'a 'b 'c 'd)
                   natural/e
                   (fin/e "x" "y"))
              14]

The implemenatation finds the ranges of natural numbers when each
finite enumeration is exhausted to compute which enumeration to use
for some index.

