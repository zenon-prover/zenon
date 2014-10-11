#  Copyright 1997 INRIA

# Reading configuration settings.
include .config_var
# Variables CAMLBYT, CAMLBIN, CAMLLEX, CAMLYACC CAMLDEP, COQC, etc. are
# defined at configuration time, and their value is recorded in .config_var

SHELL=/bin/bash

# Staging directory for package managers
DESTDIR =

CAMLFLAGS = -warn-error "$(WARN_ERROR)"

CAMLBINFLAGS = $(CAMLFLAGS) $(BIN_DEBUG_FLAGS)
CAMLBYTFLAGS = $(CAMLFLAGS) $(BYT_DEBUG_FLAGS)

ZENON_TIMEOUT = 0.1
DK_TIMEOUT = 0.1
STAT_FILE = statistics_$(ZENON_TIMEOUT)


# SOURCES specifies both the list of source files and the set of
# modules in linking order.

SOURCES = version.ml config.dummy misc.ml heap.ml globals.ml error.ml \
          progress.ml namespace.ml expr.ml \
          phrase.ml llproof.ml mlproof.ml watch.ml eqrel.ml index.ml \
          print.ml step.ml node.ml extension.ml mltoll.ml \
          parsezen.mly lexzen.mll parsetptp.mly lextptp.mll \
          parsecoq.mly lexcoq.mll parsedk.mly lexdk.mll tptp.ml \
          coqterm.ml lltocoq.ml \
          lltolj.ml lltodedukti.ml \
          enum.ml isar_case.ml lltoisar.ml \
          ext_focal.ml ext_tla.ml ext_recfun.ml \
          ext_equiv.ml ext_induct.ml \
          prove.ml checksum.dummy versionnum.ml main.ml zenon.ml

COQSRC = zenon.v zenon_coqbool.v zenon_equiv.v zenon_induct.v zenon_focal.v

DOCSRC =

TESTSRC =

OTHERSRC = INSTALL LICENSE Makefile configure .config_var.in .depend

MLSRC = $(SOURCES:%.dummy=)

MLISRC1 = $(SOURCES:%.mly=)
MLISRC2 = $(MLISRC1:%.mll=%.mli)
MLISRC3 = $(MLISRC2:%.dummy=%.mli)
MLISRC = $(MLISRC3:%.ml=%.mli)

ALLSRC = $(MLSRC) $(MLISRC) $(COQSRC) $(DOCSRC) $(TESTSRC) $(OTHERSRC)


MODULES1 = $(SOURCES:%.ml=%)
MODULES2 = $(MODULES1:%.mly=%)
MODULES3 = $(MODULES2:%.mll=%)
MODULES = $(MODULES3:%.dummy=%)

IMPL = $(MODULES:%=%.ml)
INTF = $(MODULES:%=%.mli)
BYTOBJS = $(MODULES:%=%.cmo)
BINOBJS = $(MODULES:%=%.cmx)

COQOBJ = $(COQSRC:%.v=%.vo)

# For Dedukti tests
MAKETPTP = Makefile.tptp
TPTP = ./tptp
FOFDIR = $(TPTP)/FOF
ALLDKPROPS = $(wildcard $(FOFDIR)/*.p)
ALLDKCS = $(subst $(FOFDIR),dkresults,$(ALLDKPROPS:.p=.dkc))
DKTESTDIR = ./dktest
DKAXIOMDIR = $(DKTESTDIR)/Axioms
DKPROPS = $(wildcard $(DKTESTDIR)/*.p)
DKTS = $(DKPROPS:.p=.dkt)

.PHONY: all byt bin coq

all: byt bin zenon coq

coq: $(COQOBJ)

byt: zenon.byt

bin: zenon.bin

zenon.bin: $(BINOBJS)
	$(CAMLBIN) $(CAMLBINFLAGS) -o zenon.bin $(BINOBJS)

zenon.byt: $(BYTOBJS)
	$(CAMLBYT) $(CAMLBYTFLAGS) -o zenon.byt $(BYTOBJS)

zenon: zenon.byt
	if test -x zenon.bin; then \
	  cp zenon.bin zenon; \
        else \
	  cp zenon.byt zenon; \
	fi

.PHONY: install
install:
	mkdir -p "$(DESTDIR)$(INSTALL_BIN_DIR)"
	cp zenon "$(DESTDIR)$(INSTALL_BIN_DIR)/"
	mkdir -p "$(DESTDIR)$(INSTALL_LIB_DIR)"
	cp $(COQSRC) "$(DESTDIR)$(INSTALL_LIB_DIR)/"
	for i in $(COQOBJ); \
	  do [ ! -f $$i ] || cp $$i "$(DESTDIR)$(INSTALL_LIB_DIR)/"; \
	done

.PHONY: uninstall
uninstall:
	rm -f "$(DESTDIR)$(BIN_DIR)/zenon$(EXE)"
	rm -rf "$(DESTDIR)$(LIB_DIR)/zenon"

.SUFFIXES: .ml .mli .cmo .cmi .cmx .v .vo

.ml.cmo:
	$(CAMLBYT) $(CAMLBYTFLAGS) -c $*.ml

.ml.cmx:
	$(CAMLBIN) $(CAMLBINFLAGS) -c $*.ml

.mli.cmi:
	$(CAMLBYT) $(CAMLBYTFLAGS) -c $*.mli

lexzen.ml: lexzen.mll
	$(CAMLLEX) lexzen.mll

parsezen.ml: parsezen.mly
	$(CAMLYACC) -v parsezen.mly

parsezen.mli: parsezen.ml
	:

lextptp.ml: lextptp.mll
	$(CAMLLEX) lextptp.mll

parsetptp.ml: parsetptp.mly
	$(CAMLYACC) -v parsetptp.mly

parsetptp.mli: parsetptp.ml
	:

lexcoq.ml: lexcoq.mll
	$(CAMLLEX) lexcoq.mll

parsecoq.ml: parsecoq.mly
	$(CAMLYACC) -v parsecoq.mly

parsecoq.mli: parsecoq.ml
	:

lexdk.ml: lexdk.mll
	$(CAMLLEX) lexdk.mll

parsedk.ml: parsedk.mly
	$(CAMLYACC) -v parsedk.mly

parsedk.mli: parsedk.ml
	:

config.ml: .config_var
	echo '(* This file is automatically generated. *)' >config.ml.tmp
	echo 'let libdir = "$(INSTALL_LIB_DIR)";;' >> config.ml.tmp
	if ! cmp -s config.ml config.ml.tmp; then cp config.ml.tmp config.ml; fi
	rm -f config.ml.tmp

checksum.ml: $(IMPL:checksum.ml=)
	echo '(* This file is automatically generated. *)' >checksum.ml
	echo 'let v = "'`$(SUM) $(IMPL) | $(SUM)`'";;' >>checksum.ml

.v.vo:
	$(COQC) -q $*.v

.PHONY: dist
dist: $(ALLSRC)
	mkdir -p dist/zenon
	cp $(ALLSRC) dist/zenon
	cd dist && tar cf - zenon | gzip >../zenon.tar.gz

.PHONY: doc odoc docdir
doc docdir:
	(cd doc && $(MAKE) $@)

.PHONY: clean
clean:
	cd doc; make clean
	[ ! -d test ] || (cd test; make clean)
	rm -f .#*
	rm -f *.cm* *.o *.vo *.annot *.output *.glob
	rm -f parsezen.ml parsezen.mli lexzen.ml
	rm -f parsetptp.ml parsetptp.mli lextptp.ml
	rm -f parsecoq.ml parsecoq.mli lexcoq.ml
	rm -f parsedk.ml parsedk.mli lexdk.ml
	rm -f checksum.ml
	rm -f zenon *.bin *.byt
	rm -rf dist zenon.tar.gz

.PHONY: depend
depend: $(IMPL) $(INTF) $(COQSRC)
	$(CAMLDEP) $(IMPL) $(INTF) >.depend
	$(COQDEP) -I . $(COQSRC) >>.depend

# This target downloads the TPTP archive and extract FOF problems from it in tptp/FOF/
$(FOFDIR)/.dummy: 
	make -f $(MAKETPTP) fof

# This target initializes the dktest directory
$(DKTESTDIR)/.dummy: $(FOFDIR)/.dummy
	mkdir $(DKTESTDIR)
	cp $(FOFDIR)/*001+1.p $(DKTESTDIR)
	grep -r 'Axioms/' $(DKTESTDIR) | cut -d\' -f2 | \
	awk -F'/[^/]*$$' '{printf "mkdir -p $(DKTESTDIR)/%s && cp $(TPTP)/%s $(DKAXIOMDIR);\n", $$1, $$0}' | \
	bash
	touch $(DKTESTDIR)/.dummy

.PHONY: $(wildcard $(DKTESTDIR)/*.dkt)
%.dkt: %.p
	@{ timeout $(ZENON_TIMEOUT) ./zenon -q -p0 -odedukti -itptp $<; } | { timeout $(DK_TIMEOUT) dkcheck -stdin || echo -e "\e[31mError $<\e[39m"; }

# Calls another make in order to take into account the generated files
.PHONY: dktest
dktest: $(DKTESTDIR)/.dummy
	@make dodktest

.PHONY: dodktest
dodktest: $(DKTESTDIR)/.dummy $(DKTS)

.PHONY: cleandk
cleandk:
	rm -rf $(DKTESTDIR)

.PHONY: dktestall
dktestall: $(FOFDIR)/.dummy
	rm -f $(STAT_FILE)
	rm -rf dkresults
	mkdir dkresults
	make dodktestall

# To test how changing zenon timeout impacts results, we can type (in bash)
# $ for timeout in {1..9}; do make ZENON_TIMEOUT=0.$timeout testall; done
# then proportion of zenon timeout can be computed by
# $total=$(ls tptp/FOF/ | wc -l); for timeout in {1..9}; do zto=$(grep 'zenon_exit_status 124' statistics_0.$timeout | wc -l); ch=$(grep 'dkcheck_exit_status 0' statistics_0.$timeout | wc -l); other=$(($total - $zto - ch)); echo -e "Zenon timeout:\t$zto ($((100 * $zto / $total))%)\nChecked\t\t$ch ($((100 * $ch / $total))%)\nOther:\t\t$other ($((100 * $other / $total))%)\n"; done

.PHONY: dodktestall
dodktestall: $(FOFDIR)/.dummy $(ALLDKCS)

.PHONY: $(wildcard dkresults/*.dkc)
%.dkc: %.dk
	@echo -n " ; dkcheck_timeout $(DK_TIMEOUT)" >> $(STAT_FILE)
	@/usr/bin/time --quiet -f " ; dkcheck_real_time %e ; dkcheck_exit_status %x" \
		-a -o $(STAT_FILE) \
		timeout $(DK_TIMEOUT) dkcheck -q $< || true

.SECONDARY: $(wildcard dkresults/*.dk)
dkresults/%.dk: $(FOFDIR)/%.p zenon
	@echo -n -e "file $< ; zenon_timeout $(ZENON_TIMEOUT)" >> $(STAT_FILE)
	@{ /usr/bin/time --quiet -f " ; zenon_real_time %e ; zenon_exit_status %x" \
		timeout $(ZENON_TIMEOUT) ./zenon -q -p0 -odedukti -itptp $< > $@; } \
		|& { xargs echo -n >> $(STAT_FILE); } \

include .depend
