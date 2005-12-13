#  Copyright 1997 INRIA
#  $Id: Makefile,v 1.29 2005-12-13 18:19:39 doligez Exp $

CAMLP4 = -pp 'camlp4o'
CAMLFLAGS = -warn-error A

CAMLOPT = ocamlopt
CAMLOPTFLAGS = ${CAMLFLAGS} ${OPTDEBUGFLAGS}

CAMLC = ocamlc
CAMLCFLAGS = ${CAMLFLAGS} ${BYTDEBUGFLAGS}

CAMLLEX = ocamllex
CAMLYACC = ocamlyacc

MODULES = version misc heap globals error progress expr \
          phrase llproof mlproof watch eqrel index \
          print step node extension mltoll prove \
          parsezen lexzen parsetptp lextptp parsecoq lexcoq \
          tptp \
          ext_coqbool ext_equiv coqterm lltocoq \
          main

IMPL = ${MODULES:%=%.ml}
INTF = ${MODULES:%=%.mli}
OBJBYT = ${MODULES:%=%.cmo}
OBJOPT = ${MODULES:%=%.cmx}

COQMODULES = zenon zenon_coqbool zenon_equiv
COQSRC = ${COQMODULES:%=%.v}
COQOBJ = ${COQMODULES:%=%.vo}

include .config_var

.PHONY: all
all: zenon zenon.opt zenon.byt ${COQOBJ}


zenon.opt: ${OBJOPT}
	${CAMLOPT} ${CAMLOPTFLAGS} -o zenon.opt ${OBJOPT}

zenon.byt: ${OBJBYT}
	${CAMLC} ${CAMLCFLAGS} -o zenon.byt ${OBJBYT}

zenon: zenon.opt
	cp zenon.opt zenon

.PHONY: install
install:
	mkdir -p "${BINDIR}"
	cp zenon "${BINDIR}"/
	mkdir -p "${LIBDIR}"
	cp ${COQSRC} ${COQOBJ} "${LIBDIR}"/

.PHONY: uninstall
uninstall:
	rm -f "${BINDIR}"/zenon
	cd "${LIBDIR}"; rm -f ${COQSRC} ${COQOBJ}

.PHONY: logo
logo: zenon-logo.png zenon-logo-small.png

# "gs" is ghostscript
zenon-logo.png: zenon-logo.ps
	gs -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

# "convert" is part of ImageMagick
zenon-logo-small.png: zenon-logo.png
	convert zenon-logo.png -resize 10% zenon-logo-small.png

.SUFFIXES: .ml .mli .cmo .cmi .cmx .v .vo

.ml.cmo:
	${CAMLC} ${CAMLCFLAGS} -c $*.ml

lltocoq.cmo: lltocoq.ml
	${CAMLC} ${CAMLP4} ${CAMLCFLAGS} -c lltocoq.ml

.ml.cmx:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.ml

lltocoq.cmx: lltocoq.ml
	${CAMLOPT} ${CAMLP4} ${CAMLOPTFLAGS} -c lltocoq.ml

.mli.cmi:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.mli

lexzen.ml: lexzen.mll
	${CAMLLEX} lexzen.mll

parsezen.ml: parsezen.mly
	${CAMLYACC} -v parsezen.mly

parsezen.mli: parsezen.ml
	:

lextptp.ml: lextptp.mll
	${CAMLLEX} lextptp.mll

parsetptp.ml: parsetptp.mly
	${CAMLYACC} -v parsetptp.mly

parsetptp.mli: parsetptp.ml
	:

lexcoq.ml: lexcoq.mll
	${CAMLLEX} lexcoq.mll

parsecoq.ml: parsecoq.mly
	${CAMLYACC} -v parsecoq.mly

parsecoq.mli: parsecoq.ml
	:

lexer.ml: lexer.mll
	${CAMLLEX} lexer.mll

parser.ml: parser.mly
	${CAMLYACC} -v parser.mly

parser.mli: parser.ml
	:

.v.vo:
	${COQC} $*.v

zenon_equiv.vo: zenon_equiv.v
	: ### The following command may take a few minutes to complete. ###
	${COQC} zenon_equiv.v

.PHONY: clean
clean:
	rm -f *.cmo *.cmi *.cmx *.o *.vo *.annot *.output
	rm -f parsezen.ml parsezen.mli lexzen.ml
	rm -f parsetptp.ml parsetptp.mli lextptp.ml
	rm -f parsecoq.ml parsecoq.mli lexcoq.ml
	rm -f zenon zenon.opt zenon.byt dummy_coqc8
	rm -f zenon-logo.png zenon-logo-small.png

.PHONY: archclean
archclean: clean
	rm -f .config_var

.PHONY: depend
depend: ${IMPL} ${INTF}
	ocamldep ${CAMLP4} ${IMPL} ${INTF} >.depend

include .depend
