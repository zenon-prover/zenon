#!/bin/sh
#  Copyright 2006 INRIA

# usage: equivbench.sh <n>

n=$1

awk 'BEGIN {
  print "$goal";
  for (i = 0; i < '$n'; i++){
    printf ("(<=> p_%d\n", i);
  }
  for (i = 0; i < '$n'; i++){
    printf ("(<=> p_%d\n", i);
  }
  print "True";
  for (i = 0; i < 2 * '$n'; i++){
    printf ")";
  }
  print "";
}' >equivbenchtmp.znn

awk 'BEGIN {
  print "Require Import zenon8.";
  print "Require Import zenon_equiv8.";
  for (i = 0; i < '$n'; i++){
    printf ("Parameter p_%d : Prop.\n", i);
  }
  print "Load equivbenchtmp.";
}' >equivbenchmeta.v

#time ../zenon equivbenchtmp.znn -x equiv

time ../zenon equivbenchtmp.znn -x equiv -ocoqterm8 -short >equivbenchtmp.v
wc equivbenchtmp.v
time coqc equivbenchmeta.v
