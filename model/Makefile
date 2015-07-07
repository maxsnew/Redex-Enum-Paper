MODULES := Bijection Enum Fairness Pairing UnfairPairing Sets Trace Util EvenOddPow All
VS      := $(MODULES:%=coq/%.v)

.PHONY: coq clean

test: Makefile.coq
	$(MAKE) -f Makefile.coq
	raco make -v redex-model.rkt redex-model-test.rkt \
                     redex-model-typesetting.rkt run-coq-redex-tests.rkt
	raco test redex-model-test.rkt
	raco test run-coq-redex-tests.rkt


coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R coq Enum $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
