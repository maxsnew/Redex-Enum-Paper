#lang scribble/base
@(require "cite.rkt" "util.rkt"
          scribble/manual)

@title{Myths about Random Generation and Enumeration}

Despite early, convincing studies on the value of 
random testing
@;@~cite[a b]
, random testing is unfairly
treated as a straw-man comparison. For example,
@citet[] writes:
@a-quote{
Spotting this defect requires the test case generator to 
guess a value for x such that x * 2 == x + 10 holds, 
but a random integer solves this equations with probability 
@raw-latex|{\(2^{-32}\)}|
}
When we run this example in Quickcheck@~cite[#;quickcheck],
giving it 1000 attempts to find a counter example, it finds it
about half of the time, taking about 400 attempts for each try.
Redex's random generator does a little bit better, finding it
nearly every time, typically in about 150 attempts. 
Not to single out a single paper, @citet[#;dart] uses the same
example and @citet[#;isabelle-testing] discuss this buggy
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

Our results show that, while random testing certainly does
not find all of the bugs and can sometimes take a long time
to find the bugs it does find, it is a powerful strategy
that belongs in every programmer's toolkit, especially because
it is especially easily and cheaply applied, even to complex
systems.

Whereas ad-hoc random generation strategies 
are often unfairly denegrated, randomly picking
test inputs from a uniform distribution over a
complex data-structure is often held up as an ideal, 
also without any substantial evidence.

... two more quotes.

To try to put our understanding on a firmer footing, we
have designed and built a new enumeration strategy for Redex.
Our enumerator is based on @citet[#;enumerator-something], 
but Redex's pattern language requires significant extensions
to the basic strategy (as discussed in @secref["sec:related-work"]).
We use the enumerator to provide a uniform distribution of terms
that we select from at random as well as simply iterating
through the enumeration searching for counterexamples, following
@citet[#;small-scope]'s small-scope hypothesis. 

We have also built a benchmark suite of buggy Redex programs 
together with falsifiable properties that witness the bugs. 
We evaluate the different generation strategies against
the benchmark, showing that random testing is the best overall
strategy, but that in-order enumeration finds more bugs in 
short time-frames. Selecting from the uniform distribution
is not competitive.



@;{

   related work:

- nice studies: 
  - "Heuristics for Scalable Dynamic Test Generation"
  - smallcheck paper
  - early random testing studies


section 3:

 three things.
   = (repeated) names: generate a pair; first build up the names in a table
     and then the term and then put things together

   = repeats: clever thing. turn a pair of lists into a list of pairs.

   = mismatch patterns => generate a list without duplicates

}
