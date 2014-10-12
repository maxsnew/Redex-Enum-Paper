#lang scribble/base
@(require "cite.rkt"
          scriblib/footnote
          scribble/manual)

@title[#:tag "sec:intro"]{Introduction}

This paper reports on an empirical study to better understand
the tradeoff between ad hoc random generation, in-order
enumeration and random selection from a uniform distribution
as test-case generation techniques. In order to conduct this
study we we designed and built a new
enumeration strategy that we use for enumerating Redex terms.
Our enumerator is based on @citet[bijective-term-encodings]'s, 
but Redex's pattern language requires significant extensions
to the basic strategy (as discussed in @secref["sec:related-work"]).
We use the enumerator to provide a uniform distribution of terms
that we select from at random as well as simply iterating
through the enumeration searching for counterexamples.

We have also built a benchmark suite of buggy Redex programs 
together with falsifiable properties that witness the bugs. 

We evaluate the different generation strategies against
the benchmark, showing that ad hoc random testing is the best overall
strategy, but that in-order enumeration finds more bugs in 
short time-frames. Selecting from a uniform distribution
is worse than the other two strategies on our benchmark suite.

The remainder of this paper explains our new enumeration
strategy and its application to Redex in 
@secref["sec:enum"] and @secref["sec:redex-enum"]; explains
the methodology we used in our experiments, our benchmark
suite, and our results in @secref["sec:methodology"],
@secref["sec:benchmark"], and @secref["sec:results"]; and
concludes after a discussion of related work in 
@secref["sec:related-work"] and @secref["sec:conclusion"].
