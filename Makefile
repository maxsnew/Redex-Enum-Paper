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

test:
	$(MAKE) -C model/ test

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
	mkdir -p supp/model/coq
	cp model/coq/*.v supp/model/coq
	cd supp && tar -czf supp.tar.gz * && mv supp.tar.gz .. && cd ..
	du -s -h supp.tar.gz
