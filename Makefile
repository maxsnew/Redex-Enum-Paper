all: test admit paper

paper:
	raco make -v paper.scrbl && scribble ++extra results/dominates.pdf --pdf paper.scrbl

DNE:

clean:
	rm -rf model/compiled
	$(MAKE) -C model/ clean
	rm -rf supp/model
	rm -f supp/Makefile
	rm -f supp.tar.gz

test: coq
	raco make -v model/redex-model.rkt model/redex-model-test.rkt \
                     model/redex-model-typesetting.rkt model/run-coq-redex-tests.rkt
	raco test model/redex-model-test.rkt
	raco test model/run-coq-redex-tests.rkt

coq:
	$(MAKE) -C model/ coq

admit: coq
	@echo ""
	@echo ""
	@ ! grep -i admit model/coq/*.v

supp: DNE
	cp Makefile supp/
	mkdir -p supp/model
	cp model/Makefile supp/model/
	cp model/*.rkt supp/model/
	mkdir -p supp/model/Enum
	cp model/Enum/*.v supp/model/Enum
	cd supp && tar -czf supp.tar.gz * && mv supp.tar.gz .. && cd ..
	du -s -h supp.tar.gz
