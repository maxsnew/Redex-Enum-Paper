SUPPDIR := fair-enumerations-supplementary-material

all: test admit paper

paper: DNE
	raco make -v paper.scrbl && scribble ++extra results/dominates.pdf --pdf paper.scrbl

DNE:

clean:
	rm -rf model/compiled
	$(MAKE) -C model/ clean
	rm -rf supp/model
	rm -f supp/Makefile
	rm -f supp.tar.gz

test:
	raco test enum-util.rkt
	$(MAKE) -C model/ test

coq:
	$(MAKE) -C model/ coq

admit:
	$(MAKE) -C model/ admit

supp: DNE
	rm -rf supp
	mkdir supp
	mkdir -p supp/$(SUPPDIR)
	racket results/mk-summary.rkt
	mv results/summary.rktd supp/$(SUPPDIR)
	cp supp-README.txt supp/$(SUPPDIR)/README.txt
	cp model/Makefile supp/$(SUPPDIR)
	cp model/*.rkt supp/$(SUPPDIR)
	mkdir -p supp/$(SUPPDIR)/coq
	cp model/coq/*.v supp/$(SUPPDIR)/coq
	cd supp && tar -czf $(SUPPDIR).tar.gz * && mv $(SUPPDIR).tar.gz .. && cd ..
	du -s -h $(SUPPDIR).tar.gz
