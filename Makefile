#  Copyright 1997 INRIA
#  $Id: Makefile,v 1.39 2006-03-30 13:11:26 doligez Exp $

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
          ext_coqbool ext_equiv ext_inductive coqterm lltocoq \
          checksum main

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
	mkdir -p "${DESTDIR}${BINDIR}"
	cp zenon "${DESTDIR}${BINDIR}"/
	mkdir -p "${DESTDIR}${LIBDIR}"
	cp ${COQSRC} "${DESTDIR}${LIBDIR}"/
	for i in ${COQOBJ}; do [ ! -f $$i ] || cp $$i "${DESTDIR}${LIBDIR}"; done

.PHONY: uninstall
uninstall:
	rm -f "${BINDIR}"/zenon
	cd "${LIBDIR}"; rm -f ${COQSRC} ${COQOBJ}

.SUFFIXES: .ml .mli .cmo .cmi .cmx .v .vo

.ml.cmo:
	${CAMLC} ${CAMLCFLAGS} -c $*.ml

.ml.cmx:
	${CAMLOPT} ${CAMLOPTFLAGS} -c $*.ml

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

SUMIMPL = ${IMPL:checksum.ml=}
checksum.ml: ${SUMIMPL}
	echo 'let v = "'`${SUM} ${SUMIMPL} | ${SUM}`'";;' >checksum.ml

.v.vo:
	${COQC} $*.v

.PHONY: clean
clean:
	rm -f *.cmo *.cmi *.cmx *.o *.vo *.annot *.output
	rm -f parsezen.ml parsezen.mli lexzen.ml
	rm -f parsetptp.ml parsetptp.mli lextptp.ml
	rm -f parsecoq.ml parsecoq.mli lexcoq.ml
	rm -f checksum.ml
	rm -f zenon zenon.opt zenon.byt

.PHONY: distclean
distclean: clean
	rm -f .config_var

.PHONY: depend
depend: ${IMPL} ${INTF}
	ocamldep ${CAMLP4} ${IMPL} ${INTF} >.depend
	coqdep ${COQSRC} >>.depend

include .depend
