#  Copyright 1997 INRIA
#  $Id: Makefile,v 1.18 2004-09-28 13:12:58 doligez Exp $

CAMLP4 = -pp 'camlp4o'
CAMLFLAGS = ${CAMLP4}

CAMLOPT = ocamlopt
CAMLOPTFLAGS = ${CAMLFLAGS} -p

CAMLC = ocamlc
CAMLCFLAGS = ${CAMLFLAGS} -g -dtypes

CAMLLEX = ocamllex
CAMLYACC = ocamlyacc

MODULES = version misc heap globals expr prio \
          phrase llproof mlproof eqrel index \
          print step node extension mltoll prove parser lexer tptp \
          ext_coqbool lltocoq coqterm \
          main

IMPL = ${MODULES:%=%.ml}
INTF = ${MODULES:%=%.mli}
OBJBYT = ${MODULES:%=%.cmo}
OBJOPT = ${MODULES:%=%.cmx}
ADDBYT = unix.cma
ADDOPT = unix.cmxa

COQMODULES = zenon7 zenon_coqbool7 zenon8 zenon_coqbool8
COQSRC = ${COQMODULES:%=%.v}
COQOBJ = ${COQMODULES:%=%.vo}

include .config_var

.PHONY: default
default: all

zenon.opt: ${OBJOPT}
	${CAMLOPT} ${CAMLOPTFLAGS} -o zenon.opt ${ADDOPT} ${OBJOPT}

zenon.byt: ${OBJBYT}
	${CAMLC} ${CAMLCFLAGS} -o zenon.byt ${ADDBYT} ${OBJBYT}

zenon: zenon.opt
	cp zenon.opt zenon

.PHONY: install
install:
	mkdir -p "${BINDIR}"
	cp zenon "${BINDIR}"/
	mkdir -p "${LIBDIR}"
	cp ${COQSRC} ${COQOBJ} "${LIBDIR}"/

.PHONY: logos
logos: zenon-logo.png zenon-logo-small.png

# "gs" is ghostscript
zenon-logo.png: zenon-logo.ps
	gs -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

# "convert" is part of ImageMagick
zenon-logo-small.png: zenon-logo.png
	convert zenon-logo.png -resize 10% zenon-logo-small.png

.PHONY: all
all: zenon zenon.opt zenon.byt ${COQSRC} ${COQOBJ}

.SUFFIXES: .ml .mli .cmo .cmi .cmx .v .vo

.ml.cmo:
	${CAMLC} ${CAMLCFLAGS} -c $*.ml

.ml.cmx:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.ml

.mli.cmi:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.mli

lexer.ml: lexer.mll
	${CAMLLEX} lexer.mll

parser.ml: parser.mly
	${CAMLYACC} -v parser.mly

parser.mli: parser.ml
	:

zenon7.vo: zenon7.v
	${COQC7} zenon7.v

zenon_coqbool7.vo: zenon_coqbool7.v
	${COQC7} zenon_coqbool7.v

zenon8.vo: zenon8.v
	${COQC8} zenon8.v

zenon_coqbool8.vo: zenon_coqbool8.v
	${COQC8} zenon_coqbool8.v

.PHONY: clean
clean:
	rm -f *.cmo *.cmi *.cmx *.o *.vo *.annot
	rm -f parser.ml parser.mli lexer.ml
	rm -f Makefile.bak zenon zenon.opt zenon.byt dummy_coqc8
	rm -f zenon-logo.png zenon-logo-small.png

.PHONY: depend
depend: ${IMPL} ${INTF}
	mv Makefile Makefile.bak
	(sed -e '/^#DEPENDENCIES/q' Makefile.bak; \
         ocamldep ${CAMLP4} ${IMPL} ${INTF}) \
	>Makefile

# Do NOT change anything below this line.
#DEPENDENCIES
version.cmo: version.cmi 
version.cmx: version.cmi 
misc.cmo: version.cmi misc.cmi 
misc.cmx: version.cmx misc.cmi 
heap.cmo: version.cmi heap.cmi 
heap.cmx: version.cmx heap.cmi 
globals.cmo: version.cmi globals.cmi 
globals.cmx: version.cmx globals.cmi 
expr.cmo: globals.cmi misc.cmi version.cmi expr.cmi 
expr.cmx: globals.cmx misc.cmx version.cmx expr.cmi 
prio.cmo: expr.cmi version.cmi prio.cmi 
prio.cmx: expr.cmx version.cmx prio.cmi 
phrase.cmo: expr.cmi version.cmi phrase.cmi 
phrase.cmx: expr.cmx version.cmx phrase.cmi 
llproof.cmo: expr.cmi version.cmi llproof.cmi 
llproof.cmx: expr.cmx version.cmx llproof.cmi 
mlproof.cmo: expr.cmi version.cmi mlproof.cmi 
mlproof.cmx: expr.cmx version.cmx mlproof.cmi 
eqrel.cmo: expr.cmi mlproof.cmi version.cmi eqrel.cmi 
eqrel.cmx: expr.cmx mlproof.cmx version.cmx eqrel.cmi 
index.cmo: expr.cmi globals.cmi misc.cmi mlproof.cmi version.cmi index.cmi 
index.cmx: expr.cmx globals.cmx misc.cmx mlproof.cmx version.cmx index.cmi 
print.cmo: expr.cmi index.cmi llproof.cmi mlproof.cmi phrase.cmi version.cmi \
    print.cmi 
print.cmx: expr.cmx index.cmx llproof.cmx mlproof.cmx phrase.cmx version.cmx \
    print.cmi 
step.cmo: globals.cmi print.cmi version.cmi step.cmi 
step.cmx: globals.cmx print.cmx version.cmx step.cmi 
node.cmo: expr.cmi mlproof.cmi prio.cmi version.cmi node.cmi 
node.cmx: expr.cmx mlproof.cmx prio.cmx version.cmx node.cmi 
extension.cmo: expr.cmi llproof.cmi mlproof.cmi node.cmi version.cmi \
    extension.cmi 
extension.cmx: expr.cmx llproof.cmx mlproof.cmx node.cmx version.cmx \
    extension.cmi 
mltoll.cmo: eqrel.cmi expr.cmi extension.cmi index.cmi llproof.cmi misc.cmi \
    mlproof.cmi phrase.cmi version.cmi mltoll.cmi 
mltoll.cmx: eqrel.cmx expr.cmx extension.cmx index.cmx llproof.cmx misc.cmx \
    mlproof.cmx phrase.cmx version.cmx mltoll.cmi 
prove.cmo: eqrel.cmi expr.cmi extension.cmi globals.cmi heap.cmi index.cmi \
    misc.cmi mlproof.cmi node.cmi print.cmi prio.cmi step.cmi version.cmi \
    prove.cmi 
prove.cmx: eqrel.cmx expr.cmx extension.cmx globals.cmx heap.cmx index.cmx \
    misc.cmx mlproof.cmx node.cmx print.cmx prio.cmx step.cmx version.cmx \
    prove.cmi 
parser.cmo: expr.cmi globals.cmi phrase.cmi version.cmi parser.cmi 
parser.cmx: expr.cmx globals.cmx phrase.cmx version.cmx parser.cmi 
lexer.cmo: parser.cmi version.cmi lexer.cmi 
lexer.cmx: parser.cmx version.cmx lexer.cmi 
tptp.cmo: expr.cmi lexer.cmi parser.cmi phrase.cmi version.cmi tptp.cmi 
tptp.cmx: expr.cmx lexer.cmx parser.cmx phrase.cmx version.cmx tptp.cmi 
ext_coqbool.cmo: expr.cmi extension.cmi globals.cmi index.cmi llproof.cmi \
    misc.cmi mlproof.cmi node.cmi prio.cmi version.cmi ext_coqbool.cmi 
ext_coqbool.cmx: expr.cmx extension.cmx globals.cmx index.cmx llproof.cmx \
    misc.cmx mlproof.cmx node.cmx prio.cmx version.cmx ext_coqbool.cmi 
lltocoq.cmo: expr.cmi index.cmi llproof.cmi version.cmi lltocoq.cmi 
lltocoq.cmx: expr.cmx index.cmx llproof.cmx version.cmx lltocoq.cmi 
coqterm.cmo: expr.cmi globals.cmi index.cmi llproof.cmi phrase.cmi \
    version.cmi coqterm.cmi 
coqterm.cmx: expr.cmx globals.cmx index.cmx llproof.cmx phrase.cmx \
    version.cmx coqterm.cmi 
main.cmo: coqterm.cmi eqrel.cmi extension.cmi globals.cmi lexer.cmi \
    lltocoq.cmi mltoll.cmi parser.cmi phrase.cmi print.cmi prove.cmi tptp.cmi \
    version.cmi main.cmi 
main.cmx: coqterm.cmx eqrel.cmx extension.cmx globals.cmx lexer.cmx \
    lltocoq.cmx mltoll.cmx parser.cmx phrase.cmx print.cmx prove.cmx tptp.cmx \
    version.cmx main.cmi 
prio.cmi: expr.cmi 
phrase.cmi: expr.cmi 
llproof.cmi: expr.cmi 
mlproof.cmi: expr.cmi 
eqrel.cmi: expr.cmi mlproof.cmi 
index.cmi: expr.cmi mlproof.cmi 
print.cmi: expr.cmi llproof.cmi mlproof.cmi phrase.cmi 
step.cmi: expr.cmi mlproof.cmi 
node.cmi: expr.cmi mlproof.cmi prio.cmi 
extension.cmi: expr.cmi llproof.cmi mlproof.cmi node.cmi 
mltoll.cmi: llproof.cmi mlproof.cmi phrase.cmi 
prove.cmi: expr.cmi mlproof.cmi 
parser.cmi: phrase.cmi 
lexer.cmi: parser.cmi 
tptp.cmi: phrase.cmi 
lltocoq.cmi: llproof.cmi 
coqterm.cmi: llproof.cmi phrase.cmi 
