#lang scribble/lncs

@(require scribble/manual
          redex/private/enumerator
          "enum-util.rkt")

@title[#:tag "sec:fair"]{Combinator Fairness}
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

The combinatorically-inclined reader may have noticed in our
description of @racket{cons/e} that we did not use the classic Cantor
pairing function for our bijection. Instead we used another simple
bijection that we refer to as "boxy" pairing, and called an "Elegant"
pairing function in TODO CITATION NEEDED. 

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
