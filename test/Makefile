#  Copyright 2004 INRIA
#  $Id: Makefile,v 1.3 2004-06-14 20:30:07 delahaye Exp $

.PHONY: test
test:
	@for i in test*; do \
	  echo -n $$i' '; \
	  case $$i in *.znn) fmt=z;; *.coz) fmt=focal;; *.p) fmt=tptp;; esac; \
	  if ../zenon -w -q -i$$fmt -x coqbool $$i; then \
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
