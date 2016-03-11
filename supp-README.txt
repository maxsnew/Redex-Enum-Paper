Supplementary Material

To check the coq proofs and run the Redex tests, run "make". This 
code works with Racket v6.4 and coq 8.4pl6.

The coq development is in `coq/`. If you wish to read it, start with
`Enum.v`. The Inductive corresponding to derivations from the rules in
figure 4 is `Enumerates`. The definitions corresponding to the
theorems are given in the proof overviews in section 4.  `make` builds
the model and checks to make sure there are no admitted proofs. We
have checked the proofs with coqc version 8.4pl5 and 8.4pl6.

The model used for typesetting in the paper (specifically figure 3,
but also other parts of the running text in section 5) is in
`redex-model.rkt`.

The file uniform-random-selection.pdf shows a plot in the same style
as figure 5, but comparing random selection from the enumerations to
the ad hoc random generator.

The summary.rktd file contains the data that's shown in figures 5 and
6. A plot showing all of that data plus the results of uniform
selection at random is in all-results-plot.pdf.

More details about the benchmark (describing what the benchmark
programs actually are) is available online:

   http://docs.racket-lang.org/redex/benchmark.html
