(*  Copyright 2003 INRIA  *)
(*  $Id: llproof.mli,v 1.4 2004-05-25 11:43:04 doligez Exp $  *)

open Expr;;

(* On utilise le type Expr.expr avec les restrictions suivantes:

  1. Emeta et Etau ne sont pas utilises.
  2. La distinction entre terme et proposition est respectee.
  3. Le predicat "=" a toujours deux arguments.
*)


type binop =
  | And
  | Or
  | Imply
  | Equiv
  (* ... *)
;;

(*
  Format des regles:

  H1 ... Hn
  --------- regle
      C

  H1, ... Hn, C sont des listes de propositions

  Un noeud de preuve donne la conclusion (conc), la regle (rule), et
  les sous-noeuds (hyps = [hyp_1 ... hyp_n]).
  Le noeud est valide si conc contient tous les elements de C,
  et si, pour tout i, hyp_i est inclus dans conc + Hi

  informellement, une liste P1 ... Pn represente le sequent
       P1 ... Pn |- False
  ou encore la proposition  P1 -> ... -> Pn -> False

  Un arbre valide represente la preuve de la conclusion de sa racine.

  Notation: << t1=t2 >> denote << Eapp("=",[t1;t2]) >>
*)

type rule =
  | Rfalse
    (*
       ----- Rfalse
       Efalse

     ********************)

  | Rnottrue
    (*
       ----------- Rnottrue
       Enot(Etrue)

     ********************)

  | Raxiom of expr
    (*
       ---------- Raxiom (p)
       p, Enot(p)

     ********************)

  | Rnoteq of expr
    (*
       ------------ Rnoteq t
       Enot (t = t)

     ********************)

  | Rnotnot of expr
    (*
            p
       -------------- Rnotnot p
       Enot (Enot(p))

     ********************)

  | Rconnect of binop * expr * expr
    (*
          p,q
       --------- Rconnect (And, p, q)
       Eand(p,q)

       p             q
       --------------- Rconnect (Or, p, q)
           Eor(p,q)

       Enot(p)          q
       ------------------ Rconnect (Imply, p, q)
          Eimply(p,q)

       Enot(p),Enot(q)    p,q
       ---------------------- Rconnect (Equiv, p, q)
            Eequiv(p,q)

     ********************)

  | Rnotconnect of binop * expr * expr
    (*
       Enot(p)       Enot(q)
       --------------------- Rnotconnect (And, p, q)
         Enot (Eand (p,q))

       Enot(p),Enot(q)
       ---------------- Rnotconnect (Or, p, q)
       Enot (Eor (p,q))

            p,Enot(q)
       ------------------- Rnotconnect (Imply, p, q)
       Enot (Eimply (p,q))

       Enot(p),q     p,Enot(q)
       ----------------------- Rnotconnect (Equiv, p, q)
          Enot (Eequiv,p,q))

     ********************)

  | Rex of expr * string
    (*
             P{z}
       ----------------- Rex (Eex (x, ty, P{x}, _), z)
       Eex (x, ty, P{x})

       (z n'a pas d'autre occurrence dans l'hypothese)

     ********************)

  | Rall of expr * expr    (* prop, term *)
    (*
           P{t}
       ------------------ Rall (Eall (x, ty, P{x}, _), t)
       Eall (x, ty, P{x})

     ********************)

  | Rnotex of expr * expr  (* prop, term *)
    (*
              Enot(P{t})
       ------------------------ Rnotex (Eex (x, ty, P{x}, _), t)
       Enot (Eex (x, ty, P{x}))

     *********************)

  | Rnotall of expr * string
    (*
              Enot(P{z})
       ------------------------- Rnotall (Eall (x, ty, P{x}, _), z)
       Enot (Eall (x, ty, P{x}))

       (z n'a pas d'autre occurrence dans l'hypothese)

     *********************)

  | Rpnotp of expr * expr
    (* 
       Enot (t1 = u1)        ...        Enot (tn = un)
       ----------------------------------------------- RR
       Eapp (p, [t1...tn]), Enot (Eapp (p, [u1...un]))   

       RR = Rpnotp (Eapp (p, [t1...tn]), Enot (Eapp (p, [u1...un])))

     ********************)

  | Rnotequal of expr * expr
    (*
       Enot (t1 = u1)           ...          Enot (tn = un)
       ---------------------------------------------------- RR
       Enot ((Eapp (f, [t1...tn])) = (Eapp (f, [u1...un])))

       RR = Rnotequal (Eapp (f, [t1...tn]), Eapp (f, [u1...un]))

     ********************)

  | Requalnotequal of expr * expr * expr * expr
    (*
       Enot(t1=t3),Enot(t2=t3)       Enot(t2=t4),Enot(t1=t4)
       ----------------------------------------------------- RR
                        t1=t2, Enot(t3=t4)

       RR = Requalnotequal (t1, t2, t3, t4)

     ********************)

  | Rlemma of string * string list
    (*
       ----------- Rlemma (name, args)
            C

       Si C est la conclusion de la preuve associee a "name" dans la
       liste de preuves.  Les arguments "args" correspondent aux
       parametres de "name".

     ********************)

  | Rdefinition of expr * expr
    (*
          H
         --- Rdefinition (C, H)
          C

       Si H et C sont delta-beta convertibles avec les definitions
       donnees en argument au prouveur.

    *********************)
;;

type prooftree = {
  conc : expr list;
  rule : rule;
  hyps : prooftree list;
};;

type lemma = {
  name : string;                    (* nom du lemme *)
  params : (string * string) list;  (* parametres, avec leurs types *)
  proof : prooftree;                (* preuve *)
};;

type proof = lemma list;;
