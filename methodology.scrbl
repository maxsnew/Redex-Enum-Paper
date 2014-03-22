#lang scribble/base

@(require "results/plot.rkt"
          "cite.rkt"
          scriblib/figure
          (only-in pict scale))

We compared three methods of automated test-case generation.
Two are new and use enumerations of Redex patterns as described in this 
paper, and the third is based on preexisting work and was the
first test case generator developed for Redex.

The preexisting random generator@~cite[sfp2009-kf] takes a pattern 
and a grammar as inputs and generates a random instance of the 
pattern by recursively unfolding non-terminals in the grammar, 
choosing randomly between productions.
This generator is not completely naive, and has in fact been tuned
by hand based on fairly extensive use in testing Redex models.
@; more detail...
This straightforward strategy has been an effective approach
based on past studies.@~cite[run-your-research]

We used the enumerator in two new test generation strategies,
both of which also take a pattern and a grammar as their inputs,
and construct an enumeration of the possible terms satisfying the pattern.
The first enumeration-based strategy produces random terms
by simply choosing random indexes into the enumeration.
We hoped this approach would be an improvement over the baseline
Redex generator because it chooses terms from a uniform distribution, 
whereas the baseline generator clearly does not.
For the second strategy, we used the enumerator to exhaustively
produce terms satisfying a pattern in enumerated order starting 
from index 0.

Given a method of producing random terms, the benchmark repeatedly
attempts to find a counterexample for a buggy model by generating
a term and checking it with the model's correctness property.
Our performance metric is the average interval between counterexamples 
or, for deterministic generators, the interval before the 
first counterexample is found.
When a term is generated that violates the correctness property, the
interval since the last such term is calculated and used to update
a running average. 
This process is repeated until the uncertainty in the average becomes
acceptably small or until a global cutoff for the test run elapses.
For the data in this study, we used 24 hours as the cutoff for
a single model/bug instance.
With the 43 buggy models included, that represents over a month of 
total processor time per run.

- machines
- setup (what do the scripts do)
- version of racket 
- sampling from enumeration
- p values
- distribution
- explain generation strategies
- random generation and tuning