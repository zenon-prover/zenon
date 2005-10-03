#  Copyright 2004 INRIA
#  $Id: Makefile,v 1.3.2.1 2005-10-03 10:22:30 doligez Exp $

ZOPT = -q -x coqbool -max-time 10m -max-size 500M

BENCH = test13.znn test16.znn test38.znn test41.znn test48.znn

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

coq:
	@nbok=0; nbtests=0; \
	for i in `ls *.znn`; do \
	  echo -n $$i' '; nbtests=`expr $$nbtests + 1`;\
	  ret=`../zenon -ocoq -valid $$i 1> /dev/null; echo $$?`; \
	  if test $$ret -eq 0 -o $$ret -eq 10; then \
	    echo "$$i -- Success!"; nbok=`expr $$nbok + 1`;\
	  else echo "$$i >> Fail!" ; fi ; \
	done; \
	per=`expr 100 \* $$nbok / $$nbtests`; \
	echo "$$nbok tests passed over $$nbtests, i.e. $$per%"
