all: test admit paper

paper:
	raco make -v paper.scrbl && scribble --pdf paper.scrbl

DNE:

clean:
	rm -rf model/compiled
	rm -f model/*.glob
	rm -f model/*.vo
	rm -f model/*.cache
	rm -rf supp/model
	rm -f supp/Makefile
	rm -f supp.tar.gz

test: model/Enum.vo
	raco make -v model/model.rkt model/run-coq-redex-tests.rkt
	raco test model/model.rkt
	raco test model/run-coq-redex-tests.rkt

model/Enum.vo: model/Enum.v
	coqc -R model Enum model/Enum.v

admit: model/Enum.vo
	@echo ""
	@echo ""
	@ ! grep -i admit model/*.v

supp: DNE
	cp Makefile supp/
	mkdir -p supp/model
	cp model/*.rkt supp/model/
	cp model/*.v supp/model
	cd supp && tar -czf supp.tar.gz * && mv supp.tar.gz .. && cd ..
	du -s -h supp.tar.gz
