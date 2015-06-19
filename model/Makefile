MODULES := Bijection Enum Fairness Pairing UnfairPairing Sets Trace Util EvenOddPow All
VS      := $(MODULES:%=coq/%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R coq Enum $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
