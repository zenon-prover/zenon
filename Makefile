#  Copyright 1997 INRIA
#  $Id: Makefile,v 1.6 2004-04-29 13:04:52 doligez Exp $

CAMLFLAGS = -warn-error A

CAMLOPT = ocamlopt
CAMLOPTFLAGS = ${CAMLFLAGS}

CAMLC = ocamlc
CAMLCFLAGS = ${CAMLFLAGS} -g

CAMLLEX = ocamllex
CAMLYACC = ocamlyacc

MODULES = version misc heap globals prio expr phrase llproof mlproof index \
          print step node extension mltoll prove parser lexer tptp \
          ext_coqbool \
          main

IMPL = ${MODULES:%=%.ml}
INTF = ${MODULES:%=%.mli}
OBJBYT = ${MODULES:%=%.cmo}
OBJOPT = ${MODULES:%=%.cmx}

default: all

zenon.opt: ${OBJOPT}
	${CAMLOPT} ${CAMLOPTFLAGS} -o zenon.opt ${OBJOPT}

zenon.byt: ${OBJBYT}
	${CAMLC} ${CAMLCFLAGS} -o zenon.byt ${OBJBYT}

zenon: zenon.opt
	cp zenon.opt zenon

zenon-logo.png: zenon-logo.ps
	gs -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

all: zenon zenon.opt zenon.byt

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	${CAMLC} ${CAMLCFLAGS} -c $*.ml

.ml.cmx:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.ml

.mli.cmi:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.mli

lexer.ml: lexer.mll
	${CAMLLEX} lexer.mll

parser.ml: parser.mly
	${CAMLYACC} parser.mly

parser.mli: parser.ml
	:

clean:
	rm -f *.cmo *.cmi *.cmx *.o
	rm -f parser.ml parser.mli lexer.ml
	rm -f Makefile.bak zenon zenon.opt zenon.byt

test:
	for i in test*.znn test*.coz test*.p; do \
	  echo $$i; \
	  if ./zenon -w -x coqbool $$i; then \
	    : ; \
	  else \
	    echo '>>> TEST FAILED <<<' ; \
	    break ; \
	  fi ; \
	done

depend: ${IMPL} ${INTF}
	mv Makefile Makefile.bak
	(sed -e '/^#DEPENDENCIES/q' Makefile.bak; \
         ocamldep ${IMPL} ${INTF}) \
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
prio.cmo: version.cmi prio.cmi 
prio.cmx: version.cmx prio.cmi 
expr.cmo: globals.cmi misc.cmi version.cmi expr.cmi 
expr.cmx: globals.cmx misc.cmx version.cmx expr.cmi 
phrase.cmo: expr.cmi version.cmi phrase.cmi 
phrase.cmx: expr.cmx version.cmx phrase.cmi 
llproof.cmo: expr.cmi version.cmi llproof.cmi 
llproof.cmx: expr.cmx version.cmx llproof.cmi 
mlproof.cmo: expr.cmi version.cmi mlproof.cmi 
mlproof.cmx: expr.cmx version.cmx mlproof.cmi 
index.cmo: expr.cmi globals.cmi mlproof.cmi prio.cmi version.cmi index.cmi 
index.cmx: expr.cmx globals.cmx mlproof.cmx prio.cmx version.cmx index.cmi 
print.cmo: expr.cmi index.cmi llproof.cmi mlproof.cmi phrase.cmi version.cmi \
    print.cmi 
print.cmx: expr.cmx index.cmx llproof.cmx mlproof.cmx phrase.cmx version.cmx \
    print.cmi 
step.cmo: globals.cmi print.cmi version.cmi step.cmi 
step.cmx: globals.cmx print.cmx version.cmx step.cmi 
node.cmo: expr.cmi mlproof.cmi prio.cmi version.cmi node.cmi 
node.cmx: expr.cmx mlproof.cmx prio.cmx version.cmx node.cmi 
extension.cmo: expr.cmi llproof.cmi mlproof.cmi node.cmi prio.cmi version.cmi \
    extension.cmi 
extension.cmx: expr.cmx llproof.cmx mlproof.cmx node.cmx prio.cmx version.cmx \
    extension.cmi 
mltoll.cmo: expr.cmi index.cmi llproof.cmi mlproof.cmi version.cmi mltoll.cmi 
mltoll.cmx: expr.cmx index.cmx llproof.cmx mlproof.cmx version.cmx mltoll.cmi 
prove.cmo: expr.cmi extension.cmi globals.cmi heap.cmi index.cmi mlproof.cmi \
    node.cmi print.cmi prio.cmi step.cmi version.cmi prove.cmi 
prove.cmx: expr.cmx extension.cmx globals.cmx heap.cmx index.cmx mlproof.cmx \
    node.cmx print.cmx prio.cmx step.cmx version.cmx prove.cmi 
parser.cmo: expr.cmi globals.cmi phrase.cmi version.cmi parser.cmi 
parser.cmx: expr.cmx globals.cmx phrase.cmx version.cmx parser.cmi 
lexer.cmo: parser.cmi version.cmi lexer.cmi 
lexer.cmx: parser.cmx version.cmx lexer.cmi 
tptp.cmo: expr.cmi lexer.cmi parser.cmi phrase.cmi version.cmi tptp.cmi 
tptp.cmx: expr.cmx lexer.cmx parser.cmx phrase.cmx version.cmx tptp.cmi 
ext_coqbool.cmo: expr.cmi extension.cmi globals.cmi index.cmi mlproof.cmi \
    node.cmi prio.cmi version.cmi ext_coqbool.cmi 
ext_coqbool.cmx: expr.cmx extension.cmx globals.cmx index.cmx mlproof.cmx \
    node.cmx prio.cmx version.cmx ext_coqbool.cmi 
main.cmo: extension.cmi globals.cmi lexer.cmi mlproof.cmi mltoll.cmi \
    parser.cmi phrase.cmi print.cmi prove.cmi tptp.cmi version.cmi main.cmi 
main.cmx: extension.cmx globals.cmx lexer.cmx mlproof.cmx mltoll.cmx \
    parser.cmx phrase.cmx print.cmx prove.cmx tptp.cmx version.cmx main.cmi 
phrase.cmi: expr.cmi 
llproof.cmi: expr.cmi 
mlproof.cmi: expr.cmi 
index.cmi: expr.cmi mlproof.cmi prio.cmi 
print.cmi: expr.cmi llproof.cmi mlproof.cmi phrase.cmi 
step.cmi: expr.cmi mlproof.cmi prio.cmi 
node.cmi: expr.cmi mlproof.cmi prio.cmi 
extension.cmi: expr.cmi llproof.cmi mlproof.cmi node.cmi prio.cmi 
mltoll.cmi: llproof.cmi mlproof.cmi 
prove.cmi: expr.cmi mlproof.cmi 
parser.cmi: phrase.cmi 
lexer.cmi: parser.cmi 
tptp.cmi: phrase.cmi 
