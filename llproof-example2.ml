(*  Copyright 2003 INRIA  *)


(* preuve de:
   Ex x . P => F(x) , Ex x . F(x) => P   |-   Ex x . P <=> F(x)
  On est dans Nat et on prend O comme temoin irrelevant.
*)

open Llproof;;

let p = Papply ("P", []);;
let fx = Papply ("F", [Var ("x")]);;
let fz0 = Papply ("F", [Var ("z0")]);;
let fz1 = Papply ("F", [Var ("z1")]);;
let f0 = Papply ("F", [Fapply ("O", [])]);;

let s4aa = {
  conc = [
           Neg (p);
           p;
         ];
  rule = Raxiom (p);
  hyps = [];
};;

let s4aba1a = {
  conc = [
           p;
           Neg (p);
         ];
  rule = Raxiom (p);
  hyps = [];
};;

let s4aba1b = {
  conc = [
           Neg (fz0);
           fz0;
         ];
  rule = Raxiom (fz0);
  hyps = [];
};;

let s4aba1 = {
  conc = [
           Neg (fz0);
           Neg (Connect (Equiv, p, fz0));
           Neg (p);
         ];
  rule = Rnotconnect (Equiv, p, fz0);
  hyps = [s4aba1a; s4aba1b];
};;

let s4aba = {
  conc = [
           Neg (fz0);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
           Neg (p);
         ];
  rule = Rnotex (Exists ("x", "Nat", Connect (Equiv, p, fx)), Var ("z0"));
  hyps = [s4aba1];
};;

let s4abb = {
  conc = [
           p;
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
           Neg (p);
         ];
  rule = Raxiom (p);
  hyps = [];
};;

let lemma0 = {
  conc = [
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
           Neg (p);
         ];
  rule = Rconnect (Imply, fz0, p);
  hyps = [ s4aba; s4abb ];
};;

let s4ab = {
  conc = [
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
           Neg (p);
         ];
  rule = Rlemma ("lemma0");
  hyps = [];
};;

let s4a = {
  conc = [
           Neg (p);
           Neg (Connect (Equiv, p, f0));
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rnotconnect (Equiv, p, f0);
  hyps = [s4aa; s4ab];
};;

let s4ba1a = {
  conc = [
           fz1;
           Neg (fz1);
         ];
  rule = Raxiom (fz1);
  hyps = [];
};;

let s4ba1b = {
  conc = [
           p;
           Neg (p);
         ];
  rule = Raxiom (p);
  hyps = [];
};;

let s4ba1 = {
  conc = [
           fz1;
           p;
           Neg (Connect (Equiv, p, fz1));
         ];
  rule = Rnotconnect (Equiv, p, fz1);
  hyps = [s4ba1a; s4ba1b];
};;

let s4ba = {
  conc = [
           fz1;
           p;
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rnotex (Exists ("x", "Nat", Connect (Equiv, p, fx)), Var ("z1"));
  hyps = [s4ba1];
};;

let s4bb = {
  conc = [
           Neg (p);
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rlemma ("lemma0");
  hyps = [];
};;

let s4b = {
  conc = [
           Neg (Connect (Equiv, p, f0));
           fz1;
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rnotconnect (Equiv, p, f0);
  hyps = [s4ba; s4bb];
};;

let s3 = {
  conc = [
           Connect (Imply, p, fz1);
           Neg (Connect (Equiv, p, f0));
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rconnect (Imply, p, fz1);
  hyps = [s4a; s4b];
};;

let s2 = {
  conc = [
           Exists ("x", "Nat", Connect (Imply, p, fx));
           Neg (Connect (Equiv, p, f0));
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rex (Exists ("x", "Nat", Connect (Imply, p, fx)), "z1");
  hyps = [s3];
};;

let s1 = {
  conc = [
           Exists ("x", "Nat", Connect (Imply, p, fx));
           Connect (Imply, fz0, p);
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rnotex (Exists ("x", "Nat", Connect (Equiv, p, fx)), Fapply ("O", []));
  hyps = [s2];
};;
           

let s0 = {
  conc = [
           Exists ("x", "Nat", Connect (Imply, p, fx));
           Exists ("x", "Nat", Connect (Imply, fx, p));
           Neg (Exists ("x", "Nat", Connect (Equiv, p, fx)));
         ];
  rule = Rex (Exists ("x", "Nat", Connect (Imply, fx, p)), "z0");
  hyps = [s1];
};;


let prf = [
  ("lemma0", lemma0);
  ("theorem", s0);
];;
