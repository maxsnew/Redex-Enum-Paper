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

We define an enumeration combinator @racket[c] to be a function whose
arguments are enumerators and output is an enumerator. Precisely,
@texmath{c : Enum(a_1) \cdots Enum(a_k) \to Enum(T(a_1,\cdots,a_k))}
where @texmath{T} is a type-level function. From any purely functional
enumeration we can extract 2 functions that fully define its
bijection. The first,
@texmath{args_c : \mathbb{N} \to ([\mathbb{N}],\ldots,[\mathbb{N}])}

where the output tuple has length @texmath{k}, returns the
@texmath{k}-tuple of lists of indices needed to index into the input
enumerations when decoding from a given index. The second,
@texmath{build_c : ([a_1],\ldots,[a_k]) \to T(a_1,\ldots,a_k)} is a
function that is linear in its input arguments, ensuring that all of
its inputs have to be used to construct the output. This function
builds a value of the enumeration from components from the argument
enumerations. Finally, these functions are related to the combinator
by the rule that @racket[(decode (c e_1 ... e_k) i)] must be equal to
@racketblock[(build_c (map (λ (i) (decode e_1 i)) is_1)
                      ...
                      (map (λ (i) (decode e_k i)) is_k))]
where @racket[(is_1 ... is_k)] is @racket[(arg_c i)].

We say that an enumeration combinator @racket[c] is fair if, for every
natural number @raw-latex{$m$}, there exists a natural number
@raw-latex{$M > m$} such that for every @texmath{h,j\in \{1,\ldots,k\}},

if apply @raw-latex{$args_c$} to every value greater than or equal to
@texmath{0} and less than @texmath{M}, if you concatenate all of the
lists in the @texmath{h}th column into a list @texmath{L_h} and in the
@texmath{j}th column into a list @texmath{L_j} then @texmath{L_j} will
be a permutation of @texmath{L_h}. In other words, when enumerating
all values up to @raw-latex{$M$} in the result enumeration, all used
values from argument enumerations will come from the same indices.

We say an enumeration combinator is unfair if it is not fair.

@;{TODO: update below explanation}
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


@include-section["fair-tuple.scrbl"]

@include-section["fair-union.scrbl"]
