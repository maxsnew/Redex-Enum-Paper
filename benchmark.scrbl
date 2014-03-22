#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          "line-counts.rkt"
          scriblib/figure
          scriblib/footnote
          (only-in pict scale))

The benchmark is designed to evaluate the effectiveness of
different automated testing strategies as they might be
applied by a typical user of Redex. Thus we have attempted 
to make use of models and bugs that we believe to be
representative, based on our experiences developing, 
using, and supporting Redex over the years.

The benchmark is based on six different Redex models, each
of which provides at a minimum a grammar and a soundness
predicate on terms.
In practice, most of the models consist of a dynamic semantics 
and some static well-formedness property, usually a type system.
Typically, the predicate relates the dynamic
properties of the system to the static properties,
as in type soundness.

For each model, we have manually introduced bugs into a number of
copies of the model, such that each copy is identical to the
correct version aside from a single bug. We then compare
automated testing strategies based on how well they are able 
to find counterexamples for the soundness predicates
of the buggy models.

We presume that errors come from one of three categories: 
@itemlist[
  @item{@bold{D} (Deep) Errors in the developer's understanding of the system, 
         such as when a type system really isn't sound.}
  @item{@bold{M} (Medium) Errors in the algorithm behind the
         system, such as when two judgments happen to both apply except when
         some algorithmic side-condition holds and the developer doesn't
         realize this side-condition must exist or forgets to write it down.}
  @item{@bold{S} (Shallow) Errors in the encoding of the system into Redex,
         due to typos or a misunderstanding of subtleties of Redex.}]
When discussing the bugs we have introduced, we will categorize them 
as D, M, or S errors.

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

We now discuss each of the models included in the benchmark,
along with the errors we have introduced into each model.

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

We introduced nine different bugs into the system.
stlc: 1S 2M 3S 4S 5S 6M 7M 8? 9S

@section{poly-stlc} 
This is a polymorphic version of @bold{stlc}, with
a single numeric base type, polymorphic lists, and polymorphic 
versions of the same constants. Again, the property checked is
type soundness. 9 mutations are included.

poly-stlc: 1S 2M 3S 4S 5S 6M 7M 8? 9S
 (2 is something where people generally aren't specific about what is
 a value in their semantics in LaTeX, so they might forget about this
 case. 4 might look like a D, but I can't imagine a reasonable person
 not knowing that cons should return a list and not an element; but
 this seems like a perfect example of a typo that becomes a deep
 error. 6 feels like a misunderstanding of an algorithm. 8 does not
 feel like a legitimate error, maybe you could imagine someone testing
 with a half-baked lookup and forgetting to fix it, but I can't
 imagine anyone really making this mistake during authoring.)

@section{stlc-sub} 
The same language and type system as @bold{stlc},
except that in this case all of the errors are in the substitution
function. Type soundness is checked. 9 mutations are included.

stlc-sub: 1S 2S 3S 4M 5SM

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






