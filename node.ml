(*  Copyright 2004 INRIA  *)
Version.add "$Id: node.ml,v 1.3 2004-09-09 15:25:35 doligez Exp $";;

type node = {
  nconc : Expr.expr list;
  nrule : Mlproof.rule;
  nprio : Prio.t;
  nbranches : Expr.expr list array;
};;

type node_item =
  | Node of node
  | Stop
;;

let rec xrelevant cur l accu =
  match cur, l with
  | [], [] -> assert false
  | [], h :: t -> xrelevant (Lazy.force h) t accu
  | (Stop :: _), _ -> List.rev accu
  | (Node n :: t1), t -> xrelevant t1 t (n :: accu)
;;

let relevant l = xrelevant [] l [];;
