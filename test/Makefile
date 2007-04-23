#  Copyright 2004 INRIA
#  $Id: Makefile,v 1.11 2007-04-23 17:19:11 doligez Exp $

ZOPT = -q -x coqbool -max-time 10m -max-size 500M ${RND}

BENCH = test13.znn test16.znn test38.znn test41.znn test48.znn

COQTEST = 00 01 02    04 05 06 07 08 09 \
          10 11 12 13 14 15    17 18 19 \
             21 22 23 24 25 26 27 28 29 \
	  30 31 32 33 34 35 36 37 38 39 \
             41 42 43 44 45 46 47 48 49 \
             51 52 53 54 55 56 57 58 59 \
          60 61 62 63 64 65 66 67 68 69 \
          70 71 72    74 75

COQTESTTERM = ${COQTEST}
COQTESTSCRIPT = ${COQTEST}

default: coq

.PHONY: bench
bench:
	@for i in ${BENCH}; do \
	  echo -n $$i' '; \
	  case $$i in *.znn) fmt=z;; *.coz) fmt=focal;; *.p) fmt=tptp;; esac; \
	  (/usr/bin/time -p sh -c "../zenon ${ZOPT} -i$$fmt $$i 2>&4" 2>&1 \
           | while read k t; \
	     do case $$k in user) echo $$i $$t '       ';; esac; \
	     done) \
          4>&2; \
	done

.PHONY: test
test:
	@for i in test*; do \
	  echo -n $$i' '; \
	  case $$i in *.znn) fmt=z;; *.coz) fmt=focal;; *.p) fmt=tptp;; esac; \
	  if ../zenon ${ZOPT} -i$$fmt $$i; then \
	    : ; \
	  else \
	    echo $$i '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done; \
	echo

.PHONY: coqscript coqterm coq
coqscript:
	: testing script output
	@for n in ${COQTESTSCRIPT}; do \
	  i=`echo test$$n.*`; \
	  echo -n $$i' '; \
	  case $$i in *.znn) fmt=z;; *.coz) fmt=focal;; *.p) fmt=tptp;; esac; \
	  if ../zenon ${ZOPT} -i$$fmt $$i -ocoq -context -loadpath .. \
                      >tmp_test.v \
	     && (echo -n $$i '-> coqc'; coqc -I .. tmp_test.v); then \
	    echo -n '' ; \
	  else \
	    echo $$i '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done; \
	echo
	rm -f tmp_test.v tmp_test.vo

coqterm:
	: testing term output
	@for n in ${COQTESTTERM}; do \
	  i=`echo test$$n.*`; \
	  echo -n $$i' '; \
	  case $$i in *.znn) fmt=z;; *.coz) fmt=focal;; *.p) fmt=tptp;; esac; \
	  if ../zenon ${ZOPT} -i$$fmt $$i -ocoqterm -context -loadpath .. \
                      >tmp_test.v \
	     && (echo -n $$i '-> coqc'; coqc -I .. tmp_test.v); then \
	    echo -n '' ; \
	  else \
	    echo $$i '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done; \
	echo
	rm -f tmp_test.v tmp_test.vo

coq: coqterm coqscript

clean:
	rm -f tmp_test.v tmp_test.vo
