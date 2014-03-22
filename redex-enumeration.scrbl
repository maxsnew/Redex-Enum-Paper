#lang scribble/base
@(require "util.rkt"
          "enum-util.rkt"
          scribble/manual
          redex/reduction-semantics
          redex/private/enumerator
          racket/list
          racket/pretty)

@title{Enumerating Redex Patterns}

@(define example-term-index 100000000)

Redex provides the construct @racket[define-language]
for specifying the grammar of a language. For example,
this is the grammar for the simply-typed lambda calculus,
augmented with a few numeric constants:
@racketblock/define[(define-language L
                      (e ::= 
                         (e e)
                         (λ (x : τ) e)
                         x
                         +
                         integer)
                      (τ ::= int (τ → τ))
                      (x ::= variable-not-otherwise-mentioned))]
Enumerating member of @racket[e] can be done directly
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
            (string-append line "\n"))))

There are three patterns in Redex that require special care when enumerating.
The first is repeated names. If the same meta-variable is used twice
when defining a metafunction, reduction relation, or judgment form in Redex,
then the same term must appear in both places. For example, a substitution
function will have a case with a pattern like this:
@racketblock[(subst (λ (x : τ) e_1) x e_2)]
to cover the situation where the substituted variable is the same as a
lambda parameter (in this case just returning @racket[(λ (x : τ) e_1)], since
there are no free occurrences of @racket[x] in the expression). In contrast
the two expressions @racket[e_1] and @racket[e_2] are independent since
they have different subscripts.
When enumerating patterns like this one, @racket[(subst (λ (a : int) a) a 1)]
is valid, but the term @racket[(subst (λ (a : int) a) b 1)] is not.

To handle such patterns the enumerator makes a pass over the entire term
and collects all of the variables. It then enumerates a pair where the
first component is an environment mapping the found variables to values
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
and the @racket[except/e] combinator. Here's how to generate lists of
distinct naturals:
@racketblock/define[(define (lon-without eles)
                      (fix/e (λ (lon/e)
                               (disj-sum/e 
                                (cons (fin/e null) null?)
                                (cons (dep/e 
                                       (except/e* nats/e eles)
                                       (λ (new)
                                         (lon-without (cons new eles))))
                                      cons?)))))]
where @racket[except/e*] simply calls @racket[except/e] for each element of
its input list. Here are the first @racket[12] elements of
the @racket[(lon-without '())] enumeration:
@enum-example[(lon-without '()) 12]


@;{
 three things.
   = (repeated) names: generate a pair; first build up the names in a table
     and then the term and then put things together

   = repeats: clever thing. turn a pair of lists into a list of pairs.

   = mismatch patterns => generate a list without duplicates

}