#lang scribble/base
@(require "util.rkt"
          "enum-util.rkt"
          scribble/manual
          redex
          redex/reduction-semantics
          redex/private/enumerator
          racket/list
          racket/pretty)

@title[#:tag "sec:redex-enum"]{Enumerating Redex Patterns}

@(define example-term-index 100000000)

Redex provides the construct @racket[define-language]
for specifying the grammar of a language. For example,
this is the grammar for the simply-typed lambda calculus,
augmented with a few numeric constants:
@racketblock[(define-language L
               (e ::= 
                  (e e)
                  (λ (x : τ) e)
                  x
                  +
                  integer)
               (τ ::= int (τ → τ))
               (x ::= variable-not-otherwise-mentioned))]
@(define-language L
   (e ::= 
      (e e)
      (λ (x : τ) e)
      x
      +
      integer)
   (τ ::= int (τ → τ))
   (x ::= (variable-except ||)))
Enumerating members of @racket[e] can be done directly
in terms of the combinators given in the previous section.
Members of @racket[e] are a disjoint sum of products of
either literals (like @racket[λ] and @racket[+]) or
recursive references. For example, this is the
@(add-commas example-term-index)th term:
@(apply typeset-code
        (let ([sp (open-output-string)])
          (define example (generate-term L e #:i-th example-term-index))
          (parameterize ([pretty-print-columns 40])
            (pretty-write example sp))
          (for/list ([line (in-lines (open-input-string
                                      (get-output-string sp)))])
            (string-append (regexp-replace #rx"\u0012" line "r") "\n"))))

There are three patterns in Redex that require special care when enumerating.
The first is repeated names. If the same meta-variable is used twice
when defining a metafunction, reduction relation, or judgment form in Redex,
then the same term must appear in both places. For example, a substitution
function will have a case with a pattern like this:
@racketblock[(subst (λ (x : τ) e_1) x e_2)]
to cover the situation where the substituted variable is the same as a
parameter (in this case just returning the first argument, since
there are no free occurrences of @racket[x]). In contrast
the two expressions @racket[e_1] and @racket[e_2] are independent since
they have different subscripts.
When enumerating patterns like this one, @racket[(subst (λ (a : int) a) a 1)]
is valid, but the term @racket[(subst (λ (a : int) a) b 1)] is not.

To handle such patterns the enumerator makes a pass over the entire term
and collects all of the variables. It then enumerates a pair where the
first component is an environment mapping the found variables to terms
and the second component is the rest of the term where the variables
are replaced with constant enumerations that serve as placeholders. Once
a term has been enumerated, Redex makes a pass over the term, replacing
the placeholders with the appropriate entry in the environment.

In addition to a pattern that insists on duplicate terms,
Redex also has a facility for insisting that two terms are
different from each other. For example, if we write a subscript
with @racket[__!_] in it, like this:
@racketblock[(subst (λ (x_!_1 : τ) e_1) x_!_1 e_2)]
then the two @racket[x]s must be different from each other.

Generating terms like these uses a very similar strategy to repeated
names that must be the same, except that the environment maps 
@racket[x_!_1] to a sequence of expressions whose length matches
the number of occurrences of @racket[x_!_1] and whose elements are
all different. Then, during the final phase that replaces the placeholders
with the actual terms, each placeholder gets a different element of
the list.

Generating a list without duplicates requires the @racket[dep/e] combinator
and the @racket[except/e] combinator. For example, to generate lists of distinct naturals, we first define a helper function that takes as an argument a list of numbers to exclude
@racketblock/define[(define (no-dups-without eles)
                      (fix/e (λ (lon/e)
                               (disj-sum/e 
                                (cons (fin/e null) null?)
                                (cons (dep/e 
                                       (except/e* nat/e eles)
                                       (λ (new)
                                         (no-dups-without
                                          (cons new eles))))
                                      cons?)))))]
@(define no-dups/e (no-dups-without '()))
where @racket[except/e*] simply calls @racket[except/e] for each element of
its input list. We can then define @racket[(define no-dups/e (no-dups-without '()))]
Here are the first @racket[12] elements of
the @racket[no-dups/e] enumeration:
@enum-example[no-dups/e 12]
This is the only place where dependent enumeration is used in the
Redex enumeration library, and the patterns used
are almost always infinite, so we have not encountered degenerate performance
with dependent generation in practice.

The final pattern is a variation on Kleene star that
requires that two distinct sub-sequences in a term have the
same length. 

To explain the need for this pattern, first consider the Redex pattern
@racketblock[((λ (x ...) e) v ...)]
which matches application expressions where the function position
has a lambda expression with some number of variables and
the application itself has some number of arguments. That is,
in Redex the appearance of @racket[...] indicates that the 
term before may appear any number of times, possibly none.
In this case, the term @racket[((λ (x) x) 1)] would match,
as would @racket[((λ (x y) y) 1 2)] and so we might hope
to use this as the pattern in a rewrite rule for function
application. Unfortunately, the expression
@racket[((λ (x) x) 1 2 3 4)] also matches where the first
ellipsis (the one referring to the @racket[x]) has only
a single element, but the second one (the one referring to
@racket[v]) has four elements.

In order to specify a rewrite rule that fires only when the
arity of the procedure matches the number of actual arguments
supplied, Redex allows the ellipsis itself to have a subscript.
This means not that the entire sequences are the same, but merely
that they have the same length. So, we would write:
@racketblock[((λ (x ..._1) e) v ..._1)]
which allows the first two examples in the previous paragraph,
but not the third.

To enumerate patterns like this, it is natural to think of using
a dependent enumeration, where you first pick the length of the 
sequence and then separately enumerate sequences dependent on
the list. Such a strategy is inefficient, however, because
the dependent enumeration requires constructing enumerators
during decoding. 

Instead, if we separate the pattern into two parts, first
one part that has the repeated elements, but now grouped together:
@racket[((x v) ...)]
and then the remainder in a second part (just 
@racket[(λ e)] in our example), then the enumerator can handle
these two parts with the ordinary pairing operator and, once
we have the term, we can rearrange it to match the original
pattern. 

This is the strategy that our enumerator implementation uses. Of course,
ellipses can be nested, so the full implementation is more complex,
but rearrangement is the key idea.
