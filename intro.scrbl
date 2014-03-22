#lang scribble/base
@(require "cite.rkt" "util.rkt"
          scribble/manual)

@title{Myths about Randomness and Enumeration}

Despite an early, convincing study on the value of 
random testing@~cite[an-evaluation-of-random-testing], 
random testing is often unfairly
treated as a straw-man comparison in testing papers. For example,
@citet[contract-driven-testing-of-javascript-code] write:
@a-quote{
Spotting this defect requires the test case generator to 
guess a value for x such that x * 2 == x + 10 holds, 
but a random integer solves this equation with probability 
@raw-latex|{\(2^{-32}\)}|.
}

When we run this example in Quickcheck@~cite[quickcheck],
giving it 1000 attempts to find a counter example, it finds it
about half of the time, taking on average about 400 attempts 
when it succeeds.
Redex's random generator does a little bit better, finding it
nearly every time, typically in about 150 attempts, but both
generators find this bug which very high probability. 
Not to single out a single paper, @citet[dart] use the same
example and @citet[isabelle-testing] discuss this buggy
property (the last @racket[xs] should be @racket[ys]):
@racketblock[nth (append xs ys) (length xs+n) = nth xs n]
saying that
@a-quote{
[r]andom testing typically fails to find the counterexample, even 
with hundreds of iterations, because randomly chosen values for 
@racket[n] are almost always out of bounds.
}
This property is easier for both Quickcheck and Redex,
taking, on average, 4 attempts for Quickcheck and 5 for Redex
to find a counterexample.

While we certainly agree that random testing cannot find every 
bug and better methods exist, our results show that random testing 
can be a powerful tool for bug-finding, even using a generic random
test case generator, i.e, one that is not tailored to the property being
testing. Random testing becomes especially attractive because
it is especially easily and cheaply applied, even to complex
systems.

Whereas ad-hoc random generation strategies 
are often unfairly denegrated, randomly picking
test inputs from a uniform distribution over a
complex data-structure is often held up as an ideal, 
also without any substantial evidence.

For example @citet[counting-and-generating-lambda-terms]
present a technique for selecting from a uniform
distribution of simply typable terms and argue that their
results are practical because they help ``debug compilers
or other programs manipulating terms, e.g., type checkers
or pretty printers.'' Also, 
@citet[fast-and-sound-random-generation] write than when
using a random generator like Quickcheck, ``it is very hard
not to bias the form of generated values, and thus to
unknowingly concentrate the domain of tested values to an
arbitrary subset of values.'' They go on to give a
technique for building a random generation technique that
``is uniform: the generator for a
given type and size gives the same probability to be
produced to each possible value. In a testing context this
property ensures that no subclass will be missed because
the generator is biased.'' Their paper even goes to far as to
use the word ``sound'' for random generators that are uniform.
The implication being that
Quickcheck-style random generation (or, presumably even
worse, a fixed random generator like the one in Redex
where the distribution of random terms cannot be directly adjusted
by the user of the tool) is a less-effective bug finding 
technique. These papers give no empirical evidence for why
this kind of approach to random generation results in a
set of terms that is more likely to find bugs.

To try to put our understanding on a firmer footing, we
have designed and built a new enumeration strategy for Redex.
Our enumerator is based on @citet[bijective-term-encodings]'s, 
but Redex's pattern language requires significant extensions
to the basic strategy (as discussed in @secref["sec:related-work"]).
We use the enumerator to provide a uniform distribution of terms
that we select from at random as well as simply iterating
through the enumeration searching for counterexamples.

We have also built a benchmark suite of buggy Redex programs 
together with falsifiable properties that witness the bugs. 

We evaluate the different generation strategies against
the benchmark, showing that random testing is the best overall
strategy, but that in-order enumeration finds more bugs in 
short time-frames. Selecting from the uniform distribution
is not competitive with either of the other two approaches.
