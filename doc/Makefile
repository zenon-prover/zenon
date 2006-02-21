# Copyright 2006 INRIA

REFFILES = reference.tex macros.tex \
	   install.tex options.tex input-zen.tex input-tptp.tex \
	   input-coq.tex messages.tex

all: reference.pdf

reference.pdf: ${REFFILES}
	pdflatex reference.tex
	pdflatex reference.tex

clean:
	rm -f *.aux *.dvi *.log *.toc
	rm -f reference.pdf
