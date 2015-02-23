#lang scribble/sigplan

@(require scribble/manual
          scribble/eval
          racket/list
          racket/pretty
          racket/contract
          redex/reduction-semantics
          data/enumerate/lib
          scribble/core
          "util.rkt"
          "enum-util.rkt"
          "cite.rkt")

@title[#:tag "sec:intro"]{Introduction}

@(element (style "relax" '(exact-chars)) '("~\\vspace{-.2in}"))

@(compound-paragraph (style "wrapfigure" '())
                     (list
                      (paragraph (style #f '()) 
                                 (list (element (style #f '(exact-chars)) '("{r}{1.7in}"))))
                      (paragraph (style "vspace*" '()) 
                                 (list (element (style #f '(exact-chars)) '("-.8in"))))
                      @racketblock[(define-language L
                                     (e ::= 
                                        (e e)
                                        (λ (x : τ) e)
                                        x
                                        +
                                        integer)
                                     (τ ::= int (τ → τ))
                                     (x ::= variable))]
                      (paragraph (style "vspace*" '()) 
                                 (list (element (style #f '(exact-chars)) '("-.5in"))))))
This paper reports on a new enumeration library that provides
functions that transform natural numbers into datastructures
in a way that supports property-based testing. Our primary
application of this library is in Redex, a domain-specific
programming language for operational semantics. Redex programmers
write down a high-level specification of a grammar, reduction
rules, type systems, etc., and properties that should hold for
all programs in these languages that relate, say, the reduction
semantics to the type system. Redex can then generate example
programs and test the property, looking for counterexamples. Before
this work, we largely relied on an ad hoc random generator to find
counterexamples but, inspired by the success of
Lazy Small Check@~cite[small-check] and FEAT@~cite[feat], 
we added enumeration-based generation.

@(define example-term-index 100000000)

@(define-language L
   (e ::= 
      (e e)
      (λ (x : τ) e)
      x
      +
      integer)
   (τ ::= int (τ → τ))
   (x ::= (variable-except ||)))


To give a flavor for the new capability in Redex, consider
the float above, which contains a Redex program that defines
the grammar of a simply-typed calculus plus numeric
constants. With only this much written down, a Redex programmer can ask for
first nine terms:
@enum-example[(pam/e (λ (i)
                       (generate-term L e #:i-th i))
                     natural/e
                     #:contract any/c)
              9]
or the @(add-commas example-term-index)th term:
@(apply typeset-code
        (let ([sp (open-output-string)])
          (define example (generate-term L e #:i-th example-term-index))
          (parameterize ([pretty-print-columns 40])
            (pretty-write example sp))
          (for/list ([line (in-lines (open-input-string
                                      (get-output-string sp)))])
            (string-append (regexp-replace #rx"\u0012" line "r") "\n"))))
which takes only 10 or 20 milliseconds to compute.

Thanks to our new library, we can randomly select large natural
numbers and use them as a way to generate expressions for our property-based
testing. We can also simply enumerate the first few thousand terms
and use those as inputs.

The application of our combinators significantly influenced
their design, leading us to put special emphasis on
``fair'' enumerators. At the application level, fairness
ensures that simple modifications to the Redex grammar do
not significantly change the quality of the terms that the
enumerator generates. We give a fuller discussion of
fairness in @secref["sec:fair"], after introducing our
library in @secref["sec:enum"]. @Secref["sec:redex-enum"]
connects our combinators to Redex in more detail, explaining
how we can support arbitrary Redex patterns (as they go
significantly beyond simple tree structures). 

To evaluate our combinator library, we conducted an
empirical evaluation of its performance, as compared to the
pre-existing ad hoc random generator. We compared them using
a benchmark suite of Redex programs. We give a detailed
report on the results in @secref["sec:evaluation"], but the
high-level takeaway is that our enumerators find more bugs
per second in short time-frames, while the ad hoc random
generator is more effective on long time-frames.
Accordingly, the current implementation of Redex switches
between generation modes based on the amount of time spent
testing. Finally, @secref["sec:related-work"] discusses
related work and @secref["sec:conclusion"] concludes.
