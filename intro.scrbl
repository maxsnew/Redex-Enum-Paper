#lang scribble/lncs

@(require scribble/manual
          scribble/eval
          racket/list
          racket/pretty
          redex/reduction-semantics
          redex/private/enumerator
          scribble/core
          "util.rkt"
          "enum-util.rkt"
          "cite.rkt")

@title[#:tag "sec:intro"]{Introduction}

This paper reports on a new enumeration library that provides
functions that can transform natural numbers into datastructures
in a way that supports property-based testing. Our primary
application of this library is in Redex, a domain-specific
programming language for operational semantics. Redex programmers
write down a high-level specification of a grammar, reduction
rules, type systems, etc., and properties that should hold for
all programs in these languages that relate, say, the reduction
semantics to the type system. Redex can then generate example
programs and test the property, looking for counterexamples. Before
this work, we largely relied on ad hoc random generation to generate
candidate expressions but, inspired by Lazy Small Check@~cite[small-check]
and FEAT@~cite[feat], we added enumeration-based generation.

@(define example-term-index 100000000)
To give a flavor for the new capability in Redex, here is a Redex program
that defines the grammar of a simply-typed calculus plus numeric constants:
@racketblock/define[(define-language L
                      (e ::= 
                         (e e)
                         (λ (x : τ) e)
                         x
                         +
                         integer)
                      (τ ::= int (τ → τ))
                      (x ::= variable-not-otherwise-mentioned))]
With only this much written down, a Redex programmer can then ask for the 
@(add-commas example-term-index)th term:
@(apply typeset-code
        (let ([sp (open-output-string)])
          (define example (generate-term L e #:i-th example-term-index))
          (parameterize ([pretty-print-columns 40])
            (pretty-write example sp))
          (for/list ([line (in-lines (open-input-string
                                      (get-output-string sp)))])
            (string-append (regexp-replace #rx"\u0011" line "q") "\n"))))
which takes only 10 or 20 milliseconds to compute.

Accordingly, thanks to our new library, we can select large random natural
numbers and use them as a way to randomly select expressions for our property-based
testing, as well as simply enumerating the first few thousand terms.

The application of our combinators significantly influenced
their design, leading us to a new concept for enumerators,
which we dub ``fairness''. At the application level,
fairness ensures that simple modifications to the Redex
grammar do not significantly change the quality of the terms
that the enumerator generates. We give a fuller
discussion of fairness in @secref["sec:fair"], after introducing
our library in @secref["sec:enum"].
@Secref["sec:redex-enum"] connects our combinators to Redex
in more detail, explaining how we can support arbitrary
Redex patterns (as they go significantly beyond simple tree
structures). To evaluate our combinator library, we tested
it against the ad hoc random generator on a benchmark suite
of Redex programs and report on the results in 
@secref["sec:experimental-setup"] and 
@secref["sec:results"]. @Secref["sec:related-work"]
discusses related work and @secref["sec:conclusion"]
concludes.
