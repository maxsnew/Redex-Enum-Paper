Supplementary Material

To check the coq proofs and run the Redex tests, run "make". This 
code works with Racket v6.4 and coq 8.4pl6.

The coq development is in `coq/`. Start with `Enum.v`. The Inductive
corresponding to derivations from the rules in figure 4 is
`Enumerates`. The definitions corresponding to the theorems are given
in the proof overviews in section 4.  `make` builds the model and
checks to make sure there are no admitted proofs. We have tested with
coqc version 8.4pl5.

The model used for typesetting in the paper is in `redex-model.rkt`.

The summary.rktd file contains the data that's shown in figures 5 and
6.  A plot showing all of that data is in all-results-plot.pdf. More
details about the benchmark (describing what the benchmark programs
actually are) is available online:

   http://docs.racket-lang.org/redex/benchmark.html
