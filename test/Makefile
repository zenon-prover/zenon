#  Copyright 2004 INRIA
#  $Id: Makefile,v 1.1 2004-05-27 17:20:35 doligez Exp $

.PHONY: test
test:
	for i in test*.znn; do \
	  echo -n $$i' '; \
	  if ../zenon -w -q -iz -x coqbool $$i; then \
	    : ; \
	  else \
	    echo '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done
	for i in test*.coz; do \
	  echo -n $$i' '; \
	  if ../zenon -w -q -ifocal -x coqbool $$i; then \
	    : ; \
	  else \
	    echo '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done
	for i in test*.p; do \
	  echo -n $$i' '; \
	  if ../zenon -w -q -itptp -x coqbool $$i; then \
	    : ; \
	  else \
	    echo '>>> TEST FAILED <<<' ; \
	    exit 3 ; \
	  fi ; \
	done
