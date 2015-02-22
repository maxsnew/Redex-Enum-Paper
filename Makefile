all: test admit paper

paper:
	raco make -v paper.scrbl && scribble --pdf paper.scrbl


DNE:

test:
	raco make -v model/model.rkt
	raco test model/model.rkt

model/Enum.vo: model/Enum.v
	coqc -R model Enum model/Enum.v

admit: model/Enum.vo
	@echo ""
	@echo ""
	@ ! grep -i admit model/*.v

