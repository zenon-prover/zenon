(*  Copyright 2003 INRIA  *)

open Llproof;;

let p = Papply ("P", []);;
let q = Papply ("Q", []);;

let np = Neg (p);;
let nq = Neg (q);;

let pq = Connect (Imply, p, q);;
let nqnp = Connect (Imply, nq, np);;

let s4a = {
  conc = [np; p];
  rule = Raxiom (p);
  hyps = [];
};;

let s4b = {
  conc = [q; nq];
  rule = Raxiom (q);
  hyps = [];
};;

let s3 = {
  conc = [
           pq;
           nq;
           p;
         ];
  rule = Rconnect (Imply, p, q);
  hyps = [s4a; s4b];
};;

let s2 = {
  conc = [
           pq;
           nq;
           Neg (np);
         ];
  rule = Rnotnot (p);
  hyps = [s3];
};;

let s1 = {
  conc = [
           pq;
           Neg (nqnp);
         ];
  rule = Rnotconnect (Imply, nq, np);
  hyps = [s2];
};;

let s0 = {
  conc = [ Neg (Connect (Imply, pq, nqnp)) ];
  rule = Rnotconnect (Imply, pq, nqnp);
  hyps = [s1];
};;

let prf = [ ("theorem", s0) ];;
