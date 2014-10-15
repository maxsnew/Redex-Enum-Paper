#lang scribble/lncs

@(require pict
          scribble/manual
          racket/draw
          redex/private/enumerator
          "enum-util.rkt"
          "util.rkt")

@title[#:tag "sec:fair"]{Combinator Fairness}
@section{Why Fairness?}
@;{TODO: Predictability/durability to changes, informed unfairness vs opaque unfairness}

@section{Fair Tupling}
There are multiple natural ways to generalize pairs to n-ary
tuples. Instead of constructing a new bijection function manually we
could have used a combination of the @racket[cons/e] and
@racket[map/e] combinators, giving confidence in its
correctness. Indeed, if we only cared about producing correct
bijections, this might be the best choice, however, for the purposes
of test-case generation, the produced bijection is undesirable.

@;{Verbatim moved from sec:enum}
In particular, here are two different ways to make
4-tuples of natural numbers:
@(tabular (list (list (codeblock unfair-exp)
                      (codeblock fair-exp))))

After enumerating @code{@(number->string num-enumerated)} elements,
the left-hand one has seen @max-unfair in one component but only
@min-unfair in another, whereas the right-hand one has seen at most
either @min-fair or @max-fair in all components. We refer to the
right-hand version as being "fair" and always prefer fairness in our
implementations, because it appears to correspond to the uniformity
that is perceived as valuable with enumeration. In our experience,
most of the time the obvious version of an enumerator is not fair and
the details required to tweak it are non-intuitive. In this case, the
key insight to achieve fairness is to map the leaves of the enumerated
structure to the triangle numbers.

@;{Cantor vs Boxy}
@;{TODO: cite Wolfram Conference Elegant Pairing Function}
@;{TODO: cite Tarau's n-tupling}
@;{TODO: insert math formulae}
@;{TODO: talk about finite vs infinite}

The combinatorically-inclined reader may have noticed in our
description of @racket[cons/e] that we did not use the classic Cantor
pairing function for our bijection, which can be interpreted as a more
triangular grid walk:@centered{@cantor-cons-pict[]}

Instead we used another simple bijection that we refer to as "boxy"
pairing, and called an "Elegant" pairing function in TODO CITATION
NEEDED. The two bijections are quite similar, they are both quadratic
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
@;{TODO: see if I can make this prettier...}
@centered{@raw-latex{$cantor\_pair(m, n) = \frac{(n+m)(n+m+1)}{2} + m$}}
@(centered (scale (bitmap "box_pair.png") 0.35))

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
argument given. In @cite{interting-cantor-n-tupling}, they improve on
this implementation, but the algorithm there is still a search
procedure, and we found it too slow to use in practice.

So how do we generalize boxy pairing to boxy tupling and how do we
compute an efficient inverse? A geometric interpretation gives the
answer. Every @raw-latex{$n$}-tuple whose maximal index is
@raw-latex{$k$} gets mapped to a point on an outer face of an
@raw-latex{$n$}-dimensional hypercube that whose side length is the
@raw-latex{$n$\textsuperscript{th}} power of @raw-latex{$k$}. Then, to
find where on the faces of that hypercube that the given tuple is, we
bootstrap our pairing function with a pairing function for finite
enumerations, and index into an enumeration of tuples of length
@raw-latex{$n$} whose maximal value is @raw-latex{$k$}, which can be
easily encoded using a version of @racket[list/e] that works for
finite enumerations and @racket[disj-sum/e]. Then, to invert the
bijection, we take a natural number @raw-latex{$m$} take its
@raw-latex{$k$\textsuperscript{th}} root with remainder
@raw-latex{$r$} and use @raw-latex{$r$} to index into our enumeration
of tuples with maximal value
@raw-latex{$\lfloor{\sqrt[k]{m}}\rfloor$}. Since we constructed that
as an enumeration with existing combinators, we get definitions for
both sides of the enumeration for free.

@;{Todo: in the prev para put a picture of boxy-cons, but giving alternating colors to the different "layers"}
@;{ Incorporate this example?
We can invert the geometric process by finding what face on
the n-dimensional object we've landed and then use an enumeration of
the tuples on that face. For example, when we encode @racket[42] with
@racket[cons/e], we first take the square root with remainder, giving
us a root of @racket[6] with a remainder of @racket[8] this tells us
that the largest value in the tuple is indexed with @racket[6], so we
index into an enumeration of tuples with maximum index @racket[6] with
the value @racket[8], to give us the correct value. Then boxy
generalizes by taking the nth root with remainder, while Cantor
generalizes by taking what could be called the nth simplicial root
with remainder. Efficient implementations of nth integer root are
easily available, so we use them.
}
@;{TODO: Consider putting before Fair Pairing}
@section{Fair Union}
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
