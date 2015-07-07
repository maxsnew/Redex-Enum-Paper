Supplementary Material

The coq development is in `coq/` (start with `Enum.v`). `make`
builds the model and checks to make sure there are no admitted
proofs. We have tested with coqc version 8.4pl5.

The model used for typesetting in the paper is in `model/model.rkt`.
The file `run-coq-redex-tests.rkt` tests the coq model, the
typesetting model and the actual racket implementation for agreement.

A racket snapshot build is needed to run the racket code.  For Linux
and Mac OS X users it is easy to install from source (if you have
development tools installed) by cloning https://github.com/plt/racket
and running `make` in that directory.  Nightly snapshot builds are
available at http://pre.racket-lang.org/installers/, which is easiest
for windows users and for machines without the development tools.
