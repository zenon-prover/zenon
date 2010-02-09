#  Copyright 2006 INRIA
#  $Id: Makefile,v 1.3 2010-02-09 21:08:36 weis Exp $

REFFILES = reference.tex macros.tex \
	   install.tex options.tex input-zen.tex input-tptp.tex \
	   input-coq.tex messages.tex

OBJS=reference.pdf

include ../.config_var

DOCDIR_DIR=$(DOC_DIR)/$(PROJECT_NAME)

all doc: $(OBJS)

reference.pdf: ${REFFILES}
	pdflatex reference.tex
	pdflatex reference.tex

.PHONY: logo
logo: zenon-logo.png zenon-logo-small.png

zenon-logo.png: zenon-logo.ps
	${GS} -q -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

# "convert" is part of ImageMagick
zenon-logo-small.png: zenon-logo.png
	${CONVERT} zenon-logo.png -resize 10% zenon-logo-small.png

docdir: $(OBJS)
	mkdir -p $(DOCDIR_DIR) && \
	if ! test -z $(OBJS); then \
	  cp -p $(OBJS) $(DOCDIR_DIR)/; \
	fi

clean:
	rm -f *.aux *.dvi *.log *.toc
	rm -f $(OBJS)
	rm -f zenon-logo.png zenon-logo-small.png
