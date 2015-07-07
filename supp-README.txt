Supplementary Material

The coq development is in `coq/`. Start with `Enum.v`. The Inductive
corresponding to derivations from the rules in figure 4 is
`Enumerates`. The definitions corresponding to the theorems are given
in the proof overviews in section 4.  `make` builds the model and
checks to make sure there are no admitted proofs. We have tested with
coqc version 8.4pl5.

The model used for typesetting in the paper is in `redex-model.rkt`.

A racket snapshot build is needed to run the racket code.  For Linux
and Mac OS X users it is easy to install from source (if you have
development tools installed) by cloning https://github.com/plt/racket
and running `make` in that directory.  Nightly snapshot builds are
available at http://pre.racket-lang.org/installers/, which is easiest
for windows users and for machines without the development tools.

Running `make` in the top-level type checks the Coq code, runs the
Redex tests, and the tests that compare the implementation with the
redex model and the Coq model.
