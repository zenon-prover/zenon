(*  Copyright 2004 INRIA  *)
Misc.version "$Id: node.ml,v 1.1 2004-04-01 11:37:44 doligez Exp $";;

type node = {
  nconc : Expr.expr list;
  nrule : Mlproof.rule;
  nprio : Prio.t;
  branches : Expr.expr list array;
};;
