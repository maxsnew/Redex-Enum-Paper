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
argument enumerations roughly equally, instead of indexing
deeply into one and shallowly into another one. For
example, imagine we wanted to build an enumeration for lists
of length 4. This enumeration is one way to build it:
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
the enumeration to be lists), then the
@(add-commas one-billion) element is
@code{@(format "~v" (from-nat fair-four-tuple one-billion))},
which is much more balanced. This balance is not specific to
just that index in the enumeration, either. @Figure-ref["fig:unfairness"]
shows histograms for each of the components when using
the unfair and the fair four-tuple enumerations. 
The x-coordinates of the plot correspond to the different
values that appear in the tuples and the height of each bar is
the number of times that particular number appeared when enumerating
the first @(add-commas unfairness-histograms-total-size) tuples. 
As you can see, all four components have the
same set of values for the fair tupling operation, but the first tuple
element is considerably different from the other three when using the
unfair combination.

@figure*["fig:unfairness"
         @list{Histograms of the occurrences of each natural number
               in fair and unfair tuples}
         (parameterize ([plot-width 135]
                        [plot-height 135])
           (unfairness-histograms))]

A subtle point about fairness is that we cannot restrict 
the combinators to work completely in lock-step on their argument
enumerations, or else we would not admit @emph{any} pairing operation
as fair. After all, a combinator that builds the pair
of @racket[natural/e] with itself we must eventually produce the pair
@racket['(1 . 1000)], and that pair must come either before or
after the pair @racket['(1000 . 1)]. So if we insist that at
every point in the enumeration that the combinator's result enumeration
has used all of its argument enumerations equally, then pairing would
be impossible to do fairly.

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
reaches an equilibrium point at every perfect square.

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
be an equilibrium point after 0.

Okay, so now we know that nesting pairs is not going to be fair
in general, how do we define a fair tupling operation?
As we saw in @secref["sec:enum"], the fair pair operation
traces out two of the edges of ever-increasing squares in the plane.
These ever-increasing squares are at the heart of its fairness.
In particular, the bottom-right most point in each square is
the equilibrium point, where it has used the two argument
enumerations on exactly the same set of values. 

We can generalize this idea to tracing out the faces of ever-increasing
cubes for three-tuples, and ever-increasing hypercubes in general. 
And at each dimension, there is a ``layering'' property that is preserved.
At the corners of the cubes in three dimensions, we will have traced out
all three faces of each the current cube and all of the smaller cubes
and thus have used all of the argument enumerations the same amount.
And similarly for the corners of the hypercubes in @raw-latex{$n$} dimensions.

So, we need to generalize the pairing function to compute
which face of which hypercube we are on at each point in the
enumeration. Returning to two dimensions, say we want the
44th element of the enumeration, we first compute the
integer square root, 6, and then compute the remainder (i.e.
44-6@raw-latex{$^2$}), 8. The 6 tells us that we are in the sixth layer,
where all pairs have a 6 and there are no elements larger
than 6. The remainder 8 tells us that we are at the 8th
such pair, which is @racket['(6 . 2)].

To perform the inverse, we take @racket['(6 . 2)] and identify that
its max is 6. Then we pass @racket['(6 . 2)] into the opposite
direction of the enumeration of pairs with max of 6, giving us
8. We then square the 6 and add 8 to get 44.

This process generalizes to @raw-latex{$n$} dimensions. We take the 
@raw-latex{$n$}th root to find which layer we are in. Then we take
the remainder and use that to index into an enumeration of @raw-latex{$n$}-tuples 
that has at least one @raw-latex{$n$} and whose other values are all
less than or equal to @raw-latex{$n$}. At a high-level, this has reduced the problem
from a @raw-latex{$n$}-dimension problem to an @raw-latex{$n-1$} dimensional
problem, since we can think of the faces of the @raw-latex{$n$} dimensional
hypercube as @raw-latex{$n-1$} dimensional hypercubes. It is not
just a recursive process at this point, however, since the 
@raw-latex{$n-1$} dimensional problem has the additional constraint that
the enumeration always produce @raw-latex{$n-1$} tuples containing
at least one @raw-latex{$n$} and no values larger than @raw-latex{$n$}.

We can, however, produce the enumerations inside the layers recursively.
In the general case, we need to enumerate sequences of naturals with
whose elements have a fixed maximum (i.e. the elements of the sequence
are all less than the maximum and yet the maximum definitely appears). 
This enumeration can be handled with the combinators discussed in
@secref["sec:enum"]. Specifically, an @raw-latex{$n$} tuple that contains
a maximum of @raw-latex{$m$} is either @raw-latex{$m$} consed onto the front of an
@raw-latex{$n-1$} tuple that has values between 0 and @raw-latex{$m$} or
it is a number less than @raw-latex{$m$} combined with an @raw-latex{$n-1$}
tuple that has a maximum of @raw-latex{$m$}.

@;{

As a final optimization, we found that it is faster to prime factorize
the length and then use compose @racket[list/e] calls at smaller
lengths. For instance, to enumerate lists of length @racket[6], we
enumerate pairs of lists of length @racket[3]. Composing the fair
enumerations in this way results in an enumeration that is also fair.



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



============================================================


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


}