#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          "bug-info.rkt"
          scribble/core
          scriblib/figure
          scriblib/footnote
          scribble/manual
          (only-in pict scale))

The programs in our benchmark come from two sources:
synthetic examples based on our experience with Redex over
the years and from models that we and others
have developed and bugs that were encountered during
the development process.

The benchmark has six different Redex models, each
of which provides a grammar of terms for the model
and a soundness property that is universally quantified
over those terms. Most of the models are of programming
languages and most of the soundness properties are 
type-soundness, but we also include red-black trees
and a few models come with richer properties than
just type-soundness.

For each model, we have manually introduced bugs into a
number of copies of the model, such that each copy is
identical to the correct, except for a single bug. The bugs
always manifest as a term that falsifies the soundness
property. We compare automated testing strategies based on
how quickly they are able to find counterexamples for the
soundness properties of the buggy models. Each buggy model
also has a small counterexample in its source and a test
case validating that it violates the soundness property,
ensuring that the bugs are indeed bugs and are possible to
find.

We classify each of the errors as either:
@itemlist[
  @item{@bold{D} (Deep) Errors in the developer's understanding of the system, 
         such as when a type system really isn't sound.}
  @item{@bold{M} (Medium) Errors in the algorithm behind the
         system, such as when two judgments happen to both apply except when
         some algorithmic side-condition holds and the developer doesn't
         realize this side-condition must exist or forgets to write it down.}
  @item{@bold{S} (Shallow) Errors in the encoding of the system into Redex,
         due to typos or a misunderstanding of subtleties of Redex.}]

@;{
We hope and expect that Redex should efficiently catch
shallow errors, catch many medium errors, and be only infrequently
useful in catching deep errors. Of course, it is possible for trivial
typos to manifest in deep problems and vice versa, but we hope that
generally this is true. By analogy to type systems: a deep error is
writing the wrong program, it might type check, but it's not the one
you want; a medium error is the kind of situation where a runtime
exception is thrown, the system catches it, but not beforehand and thus
maybe with more work; while a shallow error is something that you
expect the type-system to just identify.
There are exceptions of course, such as when your finger slips 
trying to write "x" and you write "y", which happens to
also be a number, transforming your program into the wrong one --
a trivial mistake that becomes a deep error.
}

Each subsection of this section introduces one of the
models in the benchmark, along with the errors we introduced
into each model.

@figure*["fig:benchmark-overview" "Benchmark Overview"]{
 @centered{
  @tabular[#:sep 
           @hspace[1]
           (cons
            (list @bold{Model}
                  @bold{LOC}
                  @bold{Bug #}
                  @bold{S/M/D}
                  @bold{Size}
                  @bold{Description of Error})
            (let ([last-model #f])
              (for/list ([t/n (in-list all-types/nums)])
                (define type (list-ref t/n 0))
                (define num (list-ref t/n 1))
                (begin0
                  (list (if (equal? last-model type)
                            ""
                            (symbol->string type))
                        (if (equal? last-model type)
                            ""
                            (get-line-count type))
                        (number->string num)
                        (symbol->string (get-category type num))
                        (number->string (get-counterexample-size type num))
                        (element (style "ErrorDescriptionBox" '())
                                 (list (get-error type num))))
                  (set! last-model type)))))]
  }
}

@section{stlc} 
A simply-typed lambda calculus with base
types of numbers and lists of numbers, including the constants
@tt{+}, which operates on numbers, and
@tt{cons}, @tt{head}, @tt{tail}, and @tt{nil} (the empty list), all
of which operate only on lists of numbers. This model has @(get-line-count 'stlc)
non-whitespace, non-comment lines of code.
The property checked is type soundness: the combination of subject reduction 
(that types are preserved by the reductions) and progress (that well-typed
non-values always take a reduction step). 

We introduced nine different bugs into this system.
The first confuses the range and domain types of the function
in the application rule, and has the small counterexample:
@racket[hd 0]. 
We consider this to be a shallow (S) bug, since it is 
essentially a typo and it is hard to imagine anyone with
any knowledge of type systems making this conceptual mistake.
Bug 2 neglects to specify that a fully applied @racket[cons]
is a value, thus the list @racket[((cons 0) nil)] violates
the progress property. We consider this be be a medium (M) bug,
as it is not a typo, but an oversight in the design of a system
that is otherwise correct in its approach.
We consider the next three bugs to be shallow (S).
Bug 3 reverses the range and the domain of function types
in the type judgment for applications. This was one of the
easiest bugs for all of our approaches to find.
Bug 4 assigns @racket[cons] a result type of @racket[int]. 
(Initially we didn't include @racket[+] as an operation in this
model, which made it impossible to observe this bug.)
The fifth bug returns the head of a list when @racket[tl]
is applied, we consider this to be a shallow bug but interestingly
it is difficult to expose: none of our methods succeeded in doing
so (see @figure-ref["fig:benchmark"]).
Bug 6 (M) only applies the @racket[hd] constant to a partially
constructed list (i.e. the term @racket[(cons 0)] instead of
@racket[((cons 0) nil)], the application of @racket[hd] to 
the second of which is indeed the smallest counterexample for
this bug.)
All of our approaches also failed to expose bugs 5 and 6.
The seventh bug, also of medium (M) severity, omits a production
from the reduction context and thus doesn't allow evaluation
on the right-hand-side of function applications.
Bug 8 always returns the type @racket[int] when looking up
a variable's type in the context.
Similarly, bug 9 (S) may return the type of an incorrect (but present)
variable from the context.

@section{poly-stlc} 
This is a polymorphic version of @bold{stlc}, with
a single numeric base type, polymorphic lists, and polymorphic 
versions of the list constants. 
No changes were made to the model except those necessary to 
make the lists constants polymorphic.
There is no type inference is the model, so all polymorphic
terms are required to be instantiated with the correct
types in order for the function to type check. 
Of course, this makes it much more difficult to automatically 
generate well-typed terms, and thus counterexamples.
Again, the property checked is
type soundness. 

All of the bugs in this system are identical to those in
@bold{stlc}, aside from any changes that had to be made
to translate them to this model, so we don't discuss them in detail.
The interesting thing here is how otherwise unrelated changes
to the system may make bugs much easier or much more difficult
to find, something we have seen time and time again in our
experience with automated testing. Comparing the results
for these two systems in @figure-ref["fig:benchmark"], we can see
indeed some bugs have become easier to find (such as bug 7) and
some have become more difficult (such as bug 2).

This model is actually a subset of the language specified in
@citet[palka-workshop], who used a specialized and optimized
QuickCheck generator for a similar type system to find bugs 
in GHC. We adapted this system (and its restriction in
@bold{stlc}) because it has already been used successfully
with random testing, which makes it a reasonable target for
an automated testing benchmark.


@;{
   Jay's comments:
poly-stlc: 1S 2M 3S 4S 5S 6M 7M 8? 9S
 (2 is something where people generally aren't specific about what is
 a value in their semantics in LaTeX, so they might forget about this
 case. 4 might look like a D, but I can't imagine a reasonable person
 not knowing that cons should return a list and not an element; but
 this seems like a perfect example of a typo that becomes a deep
 error. 6 feels like a misunderstanding of an algorithm. 8 does not
 feel like a legitimate error, maybe you could imagine someone testing
 with a half-baked lookup and forgetting to fix it, but I can't
 imagine anyone really making this mistake during authoring.)}

@section{stlc-sub} 
The same language and type system as @bold{stlc},
except that in this case all of the errors are in the substitution
function. 
Our own experience has been that it is easy to make
subtle errors when writing substitution functions, so we added
this set of tests specifically to target them with the benchmark.
There are two soundness checks for this system.
Bugs 1-5 are checked in the following way: given a candidate
counterexample, a β-redex @emph{anywhere} in the term is
reduced to get a second term, and then those two terms
are required to be Kleene-equal, or that the result of
passing both to the evaluator (which uses call-by-value
standard reduction and thus may not reduce all β-redexes)
is the same.
Bugs 4-9 are checked using type soundness for this sysem
as specified in the discussion of the @bold{stlc} model.
We included two predicates for this system because we
believe the first to be a good test for a substitution 
function but not something that a typical Redex user
would write, while the second is something one would
see in most Redex models but is less effective at
catching substitution bugs.

The first substitution bug we introduced simply omits
the case that replaces the correct variable with the
with the term to be substituted. 
We considered this to
be a shallow (S) error, and indeed all approaches were able 
to uncover it, although the time it took to do so ranged
from 1 second to around 2 minutes.
Bug 2 permutes the order of arguments when making a
recursive call. 
This was also categorized as a shallow (S)
bug, although a common one based on our experience
writing substitutions in Redex.
Bug 3 swaps the function and argument positions of
an application recurring, again essentially a typo and
a shallow error, although one of the more difficult to
find bugs in this model.

The fourth substitution bug neglects to make the renamed
bound variable ``fresh enough'' when when recurring past a lambda. 
Specifically, it ensures that the new variable is fresh
with respect to the body of the function but not the bound
or substitution variables. This bug has the rather involved
counterexample:
@centered[@racket[((λ (z int) (((λ (y1 int) (λ (y int) y)) z) 1)) 0)]]
We categorized this error as medium or deep (MD), based on
the fact that it could be attributed to either an
oversight or a fundamental misunderstanding of substitution.

Bug 5 carries out the substitution for all variables in the
term. We categorized it as SM, since it is essentially a
missing side condition, although a fairly egregious one.

Bugs 6-9 are duplicates of bugs 1-3 and bug 5, except that
they are tested with type soundness instead. (It is impossible
to detect bug 4 with this property.) 
@; this really is surprising! can't think of what else to say
@; about it right now
Surprisingly, there
is not as a clear a difference as one might expect in
the effectiveness of the two properties in our results,
although type soundness is just slightly less effective 
overall.
(See the ``sltc-sub'' models in @figure-ref["fig:benchmark"].)

@; TODO discussion for the rest of the models
@; I found in helpful to reference the table in "bugs-table.scrbl"
@; as I went though these
@section{list-machine} 
An implementation of the 
@italic{list-machine benchmark} described in @citet[list-machine],
this is a reduction semantics (as a pointer machine operating over
an instruction pointer and a store) and a type system for a
seven-instruction first-order assembly language that manipulates
@tt{cons} and @tt{nil} values. The property checked is type soundness
as specified in @citet[list-machine], namely that well-typed programs
always step or halt (``do not get stuck''). 3 mutations are included.
This was a pre-existing implementation of this system in Redex
that we adapted for the benchmark.

list-machine: 1S 2M 3S
 (2 is something that would be easy to forget needs to specified
 translating from math where you might just assume alpha-varying)

@section{rbtrees} A
model implementing red-black trees via a judgment
that a tree has the red-black property and a metafunction defining
the insert operation. The property checked is that insert preserves
the red-black tree property. 3 mutations of this model are included.

rbtrees: 1SD 2SM 3SMD
 (1 is missing a fundamental thing, as is 2. But in the case of 1 it's
 like the author didn't realize it was needed (D) but in 2 it's
 missing a step of algorithm (M), yet its also a typo because I can
 see going through a paper translating things and accidentally
 skipping a line in the translation. 3 can really fit into every
 category: it's small so that's like S, but there's a case for the
 others as well.)

@section{delim-cont}
A model of the contract and type system for
delimited control described in @citet[delim-cont-cont]. The language
is essentially PCF extended with operators for delimited continuations
and continuation marks, and contracts for those operations. 
The property checked is type soundness. 3
mutations of this model are included, one of which was found and fixed
during the original development of the model.
This was a pre-existing model developed by @citet[delim-cont-cont] which
was adapted for the benchmark.

delim-cont: 1M 2M 3SD 
 (1 is a real mistake and seems to be an algorithmic mistake. 2 is
 close to 1, and 3 is part way between a typo (S) and a misunderstanding
 of what the type of call/comp should be (D))

@section{rvm}
A preexisting model and test framework for the Racket virtual machine and
bytecode verifier.@~cite[racket-virtual-machine] 
The bugs were discovered during the development of the model and reported
in section 7 of @citet[racket-virtual-machine].
We used all of the bugs (with two exceptions)@note{We didn't include
   bugs 1 and 7 (as specified in @citet[racket-virtual-machine]) for practical
   reasons. The first affected the virtual machine model as opposed to the
   verifier, which would have required us to include the entire VM
   model in the benchmark, and the second would have required modifying
   the abstract representation of the stack in the verifier model, a global
   change that would have touched nearly every rule in the verifier.
   }that were testable as
violations of the desired ``internal properties'' of the bytecode 
verifier as specified in that effort: the totality of the verifier
over bytecode expressions, safety, and confluence, where the 
latter two state that verified expressions can be successfully
evaluated to a unique value by the virtual machine model.

rvm: 3D 4M 5M 6M 14M 15S
 (3 feels deep because "not" and "uninit" are very far from each
 other. 4 & 5 are very close to not be useful having both.)






