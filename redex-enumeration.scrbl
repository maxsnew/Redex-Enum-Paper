#lang scribble/base
@(require "util.rkt"
          "enum-util.rkt"
          "cite.rkt"
          racket/pretty
          racket/pretty
          racket/contract
          scribble/manual
          scribble/core
          scriblib/figure
          redex/reduction-semantics
          data/enumerate/lib)

@(define (paralabel . args)
   (elem #:style (style "paragraph" '()) args))

@(define example-term-index 100000000)

@(define-language L
   (e ::= 
      (e e)
      (λ (x : τ) e)
      x
      +
      natural)
   (τ ::= ℕ (τ → τ))
   (x ::= variable))

@title[#:tag "sec:redex-enum"]{Enumerating Redex Patterns}

The inspiration for our enumeration library is bringing the success of
Lazy Small Check@~cite[small-check] and FEAT@~cite[feat], 
to property-based testing for Redex programs. This section
gives an informal overview of how Redex programs are compiled
into calls to the enumeration library in preparation for
the evaluation in @secref["sec:evaluation"].

@;{
@(compound-paragraph (style "wrapfigure" '())
                     (list
                      (paragraph (style #f '()) 
                                 (list (element (style #f '(exact-chars)) '("{r}{1.7in}"))))
                      #;
                      (paragraph (style "vspace*" '()) 
                                 (list (element (style #f '(exact-chars)) '("-.8in"))))
                      @racketblock[(define-language L
                                     (e ::= 
                                        (e e)
                                        (λ (x : τ) e)
                                        x
                                        +
                                        natural)
                                     (τ ::= ℕ (τ → τ))
                                     (x ::= variable))]
                      #;
                      (paragraph (style "vspace*" '()) 
                                 (list (element (style #f '(exact-chars)) '("-.5in"))))))
}

@figure["fig:redex-example" "Simply-Typed λ-Calculus"]{
 @centered{
 @racketblock[(define-language L
                (e ::= 
                   (e e)
                   (λ (x : τ) e)
                   x
                   +
                   natural)
                (τ ::= ℕ (τ → τ))
                (x ::= variable))]
}}

Redex programmers write down a high-level specification of a grammar, reduction
rules, type system, etc., and properties that should hold for
programs in these languages that relate, say, the reduction
semantics to the type system. Redex can then generate example
programs and try to falsify the properties.

To give a flavor for the new capability in Redex, consider
the language in @figure-ref["fig:redex-example"], which contains a Redex program that defines
the grammar of a simply-typed calculus, plus numeric
constants. With only this much written down, a Redex programmer can ask for
the first nine terms:
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

Our extensions to Redex map each different pattern that can appear
in a grammar definition into an enumeration. At a high-level, the correspondence
between Redex patterns and our combinators is clear, namely recursive non-terminals map
into uses of @racket[dep/e], alternatives map into @racket[or/e] and 
sequences map into @racket[list/e]. We also take care to exploit
our library's fairness. In particular, when enumerating the pattern, 
@racket[(λ (x : τ) e)], we do not generate list and pair patterns
following the precise structure, which would lead to an unfair nesting.
Instead, we generate the pattern @racket[(list/e x/e τ/e e/e)], where
@racket[x/e], @racket[τ/e] and @racket[e/e] correspond to the enumerations
for those non-terminals, and use @racket[map/e] to construct the
actual term.

Redex's pattern language is more general, however, and there are four
issues in Redex patterns that require special care when enumerating.

@paralabel{Patterns with repeated names} If the same meta-variable is used twice
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

To handle such patterns the enumeration makes a pass over the entire term
and collects all of the variables. It then enumerates a pair where the
first component is an environment mapping the found variables to terms
and the second component is the rest of the term where the variables
are replaced with constant enumerations that serve as placeholders. Once
a term has been enumerated, Redex makes a pass over the term, replacing
the placeholders with the appropriate entry in the environment. This strategy
also ensures that we generate a fair enumeration of each pattern, rather
than introducing unwanted nesting.

@paralabel{Patterns with inequalities}
Second, in addition to patterns that insists on duplicate terms,
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
and the @racket[except/e] combinator. For example, to generate lists of distinct naturals, 
we first define a helper function that takes as an argument a list of numbers to exclude
@racketblock/define[(define (no-dups-without eles)
                      (or/e (fin/e null)
                            (dep/e 
                             (except/e* natural/e eles)
                             (λ (new)
                               (delay/e
                                (no-dups-without
                                 (cons new eles)))))))]
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

@paralabel{List patterns with length constraints}
The third complex aspect of Redex patterns is Redex's variation on Kleene star that
requires that two distinct sub-sequences in a term have the same length. 

To explain these kinds of patterns, first consider the Redex pattern
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
the dependent enumeration requires constructing enumerations
during decoding. 

Instead, if we separate the pattern into two parts, first
one part that has the repeated elements, but now grouped together:
@racket[((x v) ...)]
and then the remainder in a second part (just 
@racket[(λ e)] in our example), then the enumeration can handle
these two parts with the ordinary pairing operator and, once
we have the term, we can rearrange it to match the original
pattern. 

This is the strategy that our enumeration implementation uses. Of course,
ellipses can be nested, so the full implementation is more complex,
but rearrangement is the key idea.

@paralabel{Ambiguous patterns}
And finally, there is one relatively uncommon use of Redex's patterns 
that we cannot enumerate. It is a bit technical and explaining it requires
first explaining ambiguity in matching Redex patterns. There are
several different ways that a Redex grammar definition can be ambiguous.
The simplest one is when a single non-terminal has overlapping productions,
but it can occur due to multiple uses of ellipses in a single sequence or
when matching @racket[in-hole]. Because of the way our enumeration compilation 
works, we are not technically building a bijection between the naturals
and terms in a Redex pattern; it is more accurate to say we are building
a bijection between the naturals and the ways one might parse a Redex pattern.
In our implementation, of course, we construct a concrete term from the
parse, but when a pattern is ambiguous there may be a single term
that corresponds to multiple parses and thus our enumeration is not bijective.
Usually, this is not a problem, as we ultimately need only the mapping
from naturals to Redex patterns, not the inverse. There is one situation,
however, where we need the inverse, namely to handle patterns with 
inequalities, as discussed above. Determining if a pattern is ambiguous
in the general case is a computationally difficult task, so we approximate
it in a way that works well for Redex models we encounter in practice 
(since few Redex languages are intentionally ambiguous), but if we cannot
determine that a pattern is unambiguous and it is combined with a
@racket[__!_] pattern, Redex will signal an error instead of enumerating
the pattern.

@section{Fairness and Redex}

Fair combinators give us predictability for programs that
use our enumerations. In Redex, our main application of
enumeration combinators, fairness ensures that when a Redex
programmer makes an innocuous change to the grammar of
the language (e.g. changing the relative order of two
sub-expressions in an expression form) the enumeration
quality is not significantly affected. For example, consider
an application expression. From the perspective of the
enumeration, an application expression looks just like a list
of expressions. An unfair enumeration might cause our
bug-finding search to spend a lot of time generating
different argument expressions and always using similar
(simple, boring) function expressions. 

Of course, the flip-side of this coin is that using unfair
combinators can improve the quality of the search in
some cases, even over fair enumeration. For example, when we
are enumerating expressions that consist of a choice between
variables and other kinds of expressions, we do not want to
spend lots of time trying out different variables because most
models are sensitive only to when variables differ from 
each other, not their exact spelling. Accordingly unfairly
biasing our enumerations away from different variables 
can be a win for finding bugs. Overall, however, it is important
that we do have a fair set of combinators that correspond
to the way that Redex programs are constructed and then when
Redex programs are compiled into the combinators, the compilation
can use domain knowledge about Redex patterns to selectively
choose targeted unfairness, but still use fair combinators when it
has no special knowledge.
