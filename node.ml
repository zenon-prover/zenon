(*  Copyright 2004 INRIA  *)
Version.add "$Id: node.ml,v 1.2 2004-04-29 13:04:52 doligez Exp $";;

type node = {
  nconc : Expr.expr list;
  nrule : Mlproof.rule;
  nprio : Prio.t;
  branches : Expr.expr list array;
};;
