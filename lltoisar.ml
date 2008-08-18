(*  Copyright 2008 INRIA  *)
Version.add "$Id: lltoisar.ml,v 1.1 2008-08-18 09:39:11 doligez Exp $";;

open Printf;;

open Expr;;
open Llproof;;
open Namespace;;

let getname e = sprintf "%s%x" hyp_prefix (Index.get_number e);;

let tauname e = sprintf "%s%d" tau_prefix (Index.get_number e);;

let rec p_list init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init printer x;
  | h::t ->
      fprintf oc "%s%a%s" init printer h sep;
      p_list init printer sep oc t;
;;

let rec p_expr oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "arbitrary";
  | Evar (v, _) ->
      poc "%s" v;
  | Eapp ("=", [e1; e2], _) ->
      poc "(%a = %a)" p_expr e1 p_expr e2;
  | Eapp ("=", l, _) -> p_expr oc (eapp ("(op =)", l))
  | Eapp ("$match", e1 :: l, _) -> assert false (* TODO *)
  | Eapp (f, l, _) ->
      poc "(%s%a)" f p_expr_list l;
  | Enot (e, _) ->
      poc "(~%a)" p_expr e;
  | Eand (e1, e2, _) ->
      poc "(%a&%a)" p_expr e1 p_expr e2;
  | Eor (e1, e2, _) ->
      poc "(%a|%a)" p_expr e1 p_expr e2;
  | Eimply (e1, e2, _) ->
      poc "(%a-->%a)" p_expr e1 p_expr e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<->%a)" p_expr e1 p_expr e2;
  | Etrue ->
      poc "True";
  | Efalse ->
      poc "False";
  | Eall (Evar (x, _), t, e, _) ->
      poc "(ALL %s. %a)" x p_expr e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), t, e, _) ->
      poc "(EX %s. %a)" x p_expr e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), t, e, _) -> assert false (* TODO *)
  | Elam _ -> assert false
  | Emeta _ -> assert false
  | Etau _ -> poc "%s" (tauname e);  (* FIXME *)

and p_expr_list oc l = p_list " " p_expr "" oc l;
;;

let p_is oc h =
  match h with
  | Eand (e1, e2, _) ->
     fprintf oc "(is\"?%s&?%s\")\n" (getname e1) (getname e2);
  | Eor (e1, e2, _) ->
     fprintf oc "(is\"?%s|?%s\")\n" (getname e1) (getname e2);
  | Eimply (e1, e2, _) ->
     fprintf oc "(is\"?%s-->?%s\")\n" (getname e1) (getname e2);
  | Eequiv (e1, e2, _) ->
     fprintf oc "(is\"?%s<->?%s\")\n" (getname e1) (getname e2);
  | Enot (Eand (e1, e2, _), _) ->
     fprintf oc "(is\"~(?%s&?%s)\")\n" (getname e1) (getname e2);
  | Enot (Eor (e1, e2, _), _) ->
     fprintf oc "(is\"~(?%s|?%s)\")\n" (getname e1) (getname e2);
  | Enot (Eimply (e1, e2, _), _) ->
     fprintf oc "(is\"~(?%s-->?%s)\")\n" (getname e1) (getname e2);
  | Enot (Eequiv (e1, e2, _), _) ->
     fprintf oc "(is\"~(?%s<->?%s)\")\n" (getname e1) (getname e2);
  | Eall (v, t, e1, _) ->
     fprintf oc "(is\"ALL x. ?%s x\")\n" (getname (elam (v, t, e1)));
  | Eex (v, t, e1, _) ->
     fprintf oc "(is\"EX x. ?%s x\")\n" (getname (elam (v, t, e1)));
  | Enot (Eall (v, t, e1, _), _) ->
     fprintf oc "(is\"~(ALL x. ?%s x)\")\n" (getname (elam (v, t, e1)));
  | Enot (Eex (v, t, e1, _), _) ->
     fprintf oc "(is\"~(EX x. ?%s x)\")\n" (getname (elam (v, t, e1)));
  | Enot (Enot (e1, _), _) ->
     fprintf oc "(is\"~~?%s\")\n" (getname e1);
  | _ -> fprintf oc "\n"
;;

type signed =
  | P of expr
  | N of expr
;;

let p_assume oc h =
  let (hh, pre, ref) =
    match h with
    | P e -> (e, "", e)
    | N e -> (enot e, "~", e)
  in
  fprintf oc "assume %s:\"%s?%s\"" (getname hh) pre (getname ref);
  p_is oc hh;
;;

let p_sequent oc hs =
  List.iter (p_assume oc) hs;
  fprintf oc "show False\n";
;;

let apply lam arg =
  match lam with
  | Elam (v, t, e1, _) -> substitute [(v, arg)] e1
  | _ -> assert false
;;

let rec p_tree oc proof =
  match proof.rule with
  | Rconnect (And, e1, e2) ->
     p_alpha oc "and" (eand (e1, e2)) [P e1; P e2] proof.hyps;
  | Rconnect (Or, e1, e2) ->
     p_beta oc "or" (eor (e1, e2)) [[P e1]; [P e2]] proof.hyps;
  | Rconnect (Imply, e1, e2) ->
     p_beta oc "imply" (eimply (e1, e2)) [[N e1]; [P e2]] proof.hyps;
  | Rconnect (Equiv, e1, e2) ->
     p_beta oc "equiv" (eequiv (e1, e2)) [[N e1; N e2]; [P e1; P e2]]
            proof.hyps;
  | Rnotconnect (And, e1, e2) ->
     p_beta oc "notand" (enot (eand (e1, e2))) [[N e1]; [N e2]] proof.hyps;
  | Rnotconnect (Or, e1, e2) ->
     p_alpha oc "notor" (enot (eor (e1, e2))) [N e1; N e2] proof.hyps;
  | Rnotconnect (Imply, e1, e2) ->
     p_alpha oc "notimply" (enot (eimply (e1, e2))) [P e1; N e2] proof.hyps;
  | Rnotconnect (Equiv, e1, e2) ->
     p_beta oc "notequiv" (enot (eequiv (e1, e2)))
            [[N e1; P e2]; [P e1; N e2]] proof.hyps;
  | Rextension _ -> assert false (* TODO *)
  | Rnotnot (e1) ->
     p_alpha oc "notnot" (enot (enot e1)) [P e1] proof.hyps;
  | Rex (Eex (x, t, e1, _) as p, v) ->
     p_delta oc "ex" p v false (elam (x, t, e1)) proof.hyps;
  | Rex _ -> assert false
  | Rnotall (Eall (x, t, e1, _) as p, v) ->
     p_delta oc "notall" p v true (elam (x, t, e1)) proof.hyps;
  | Rnotall _ -> assert false
  | Rall (Eall (x, t, e1, _), e2) ->
     p_gamma oc "all" false (elam (x, t, e1)) e2 proof.hyps;
  | Rall _ -> assert false
  | Rnotex (Eex (x, t, e1, _), e2) ->
     p_gamma oc "notex" true (elam (x, t, e1)) e2 proof.hyps;
  | Rnotex _ -> assert false
  | Rlemma (l, a) ->
     fprintf oc "by (rule %s [of" l;
     List.iter (fun x -> fprintf oc " %s" x) a;
     fprintf oc "])\n";
  | Rcut (e1) ->
     fprintf oc "proof (rule zenon_em[of ";
     p_expr oc e1;
     fprintf oc "])\n";
     let rec p_sub l1 l2 =
       match l1, l2 with
       | [], [] -> ()
       | [h], [t] ->
          p_sequent oc h;
          p_tree oc t;
          fprintf oc "qed\n";
       | h::hs, t::ts ->
          p_sequent oc h;
          p_tree oc t;
          fprintf oc "next\n";
       | _ -> assert false
     in p_sub [[P e1]; [N e1]] proof.hyps;
  | Raxiom (e1) ->
     let ne1 = getname e1 in
     let nne1 = getname (enot e1) in
     fprintf oc "apply (rule notE [OF %s %s])done\n" nne1 ne1;
  | Rdefinition _ -> assert false (* TODO *)
  | Rnotequal _ -> assert false (* TODO *)
  | Rpnotp _ -> assert false (* TODO *)
  | Rnoteq e1 ->
     let nh = getname (enot (eapp ("=", [e1; e1]))) in
     fprintf oc "apply(rule zenon_noteq[OF %s])done\n" nh;
  | Rnottrue ->
     let nh = getname (enot etrue) in
     fprintf oc "apply(rule zenon_nottrue[OF %s])done\n" nh;
  | Rfalse ->
     fprintf oc "apply(rule %s)done\n" (getname efalse);

and p_alpha oc lem h0 hs sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let n0 = getname h0 in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n0;
  p_sequent oc hs;
  p_tree oc t;
  fprintf oc "qed\n";

and p_beta oc lem h0 hs sub =
  let n0 = getname h0 in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n0;
  let rec p_sub l1 l2 =
    match l1, l2 with
    | [], [] -> ()
    | [h], [t] ->
       p_sequent oc h;
       p_tree oc t;
       fprintf oc "qed\n";
    | h::hs, t::ts ->
       p_sequent oc h;
       p_tree oc t;
       fprintf oc "next\n";
       p_sub hs ts;
    | _ -> assert false
  in p_sub hs sub;

and p_gamma oc lem neg lam e sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, ns) = if neg then (enot, "~") else ((fun x -> x), "") in
  let nlam = getname lam in
  let body = ng (apply lam e) in
  let nbody = getname body in
  fprintf oc "proof (rule zenon_%s[of \"?%s\" \"" lem nlam;
  p_expr oc e;
  fprintf oc "\"], assumption)\n";
  fprintf oc "assume %s: \"%s?%s " nbody ns nlam;
  p_expr oc e;
  fprintf oc "\"";
  p_is oc body;
  fprintf oc "show False\n";
  p_tree oc t;
  fprintf oc "qed\n";

and p_delta oc lem h0 v neg lam sub =
  let t = match sub with [t] -> t | _ -> assert false in
  let (ng, ns) = if neg then (enot, "~") else ((fun x -> x), "") in
  let h00 = ng h0 in
  let n00 = getname h00 in
  let nlam = getname lam in
  fprintf oc "proof (rule zenon_%s[OF %s])\n" lem n00;
  fprintf oc "fix %s\n" v;
  let h =
    match lam with
    | Elam (x, _, e1, _) -> ng (substitute [(x, evar (v))] e1)
    | _ -> assert false
  in
  fprintf oc "assume %s: \"%s?%s %s\"" (getname h) ns nlam v;
  p_is oc h;
  fprintf oc "show False\n";
  p_tree oc t;
;;

let p_lemma oc lem =
  fprintf oc "lemma %s:\n" lem.name;
  List.iter (fun (x, y) -> fprintf oc " fixes \"%s\"\n" x) lem.params;
  let p_asm x =
    fprintf oc " assumes %s:\"" (getname x);
    p_expr oc x;
    fprintf oc "\"";
    p_is oc x;
  in
  List.iter p_asm lem.proof.conc;
  fprintf oc " shows \"False\"\n";
  p_tree oc lem.proof;
;;

let p_theorem oc lem ngoal =
  fprintf oc "theorem %s:\n" lem.name;
  List.iter (fun (x, y) -> fprintf oc " fixes \"%s\"\n" x) lem.params;
  let goal =
    match ngoal with
    | Enot (e1, _) -> e1
    | _ -> assert false
  in
  let hyps = List.filter (fun x -> x <> ngoal) lem.proof.conc in
  let p_asm x =
    fprintf oc " assumes %s:\"" (getname x);
    p_expr oc x;
    fprintf oc "\"";
    p_is oc x;
  in
  List.iter p_asm hyps;
  fprintf oc " shows \"";
  p_expr oc goal;
  fprintf oc "\"(is \"?%s\")\n" (getname goal);
  fprintf oc "proof (rule zenon_nnpp)\n";
  p_sequent oc [N goal];
  p_tree oc lem.proof;
  fprintf oc "qed\n";
;;

let rec p_lemmas oc llp ngoal =
  match llp with
  | [] -> assert false
  | [x] -> p_theorem oc x ngoal;
  | h::t -> p_lemma oc h; p_lemmas oc t ngoal;
;;

let rec get_goal phrases =
  match phrases with
  | [] -> efalse
  | Phrase.Hyp (n, e, _) :: t when n = goal_name -> e
  | _ :: t -> get_goal t
;;

let output oc phrases llp =
  if !Globals.ctx_flag then assert false; (* TODO *)
  if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
  p_lemmas oc llp (get_goal phrases);
  if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
  !Coqterm.constants_used
;;
