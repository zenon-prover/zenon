#  Copyright 2004 INRIA
#  $Id: Makefile,v 1.2 2004-06-04 09:24:11 doligez Exp $

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
