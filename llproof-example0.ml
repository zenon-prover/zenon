(*  Copyright 2003 INRIA  *)

(* preuve de P\/Q -> Q\/P *)

open Llproof;;

let p = Papply ("P", []);;
let q = Papply ("Q", []);;

let np = Neg (p);;
let nq = Neg (q);;

let pq = Connect (Or, p, q);;
let qp = Connect (Or, q, p);;
let nqp = Neg (qp);;

let s3a = {
  conc = [ p; np ];
  rule = Raxiom (p);
  hyps = [];
};;

let s3b = {
  conc = [ nq; q ];
  rule = Raxiom (q);
  hyps = [];
};;

let s2 = {
  conc = [ pq; np; nq ];
  rule = Rconnect (Or, p, q);
  hyps = [ s3a; s3b ];
};;

let s1 = {
  conc = [ pq; nqp ];
  rule = Rnotconnect (Or, q, p);
  hyps = [ s2 ];
};;

let s0 = {
  conc = [ Neg (Connect (Imply, pq, qp)) ];
  rule = Rnotconnect (Imply, pq, qp);
  hyps = [ s1 ];
};;


let prf = [ ("theorem", s0) ];;
