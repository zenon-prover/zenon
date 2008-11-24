(*  Copyright 2004 INRIA  *)
Version.add "$Id: lltocoq.ml,v 1.40 2008-11-24 15:28:27 doligez Exp $";;

open Printf;;

open Expr;;
open Llproof;;
open Namespace;;

let rec p_list init printer sep oc l =
  match l with
  | [] -> ()
  | [x] -> fprintf oc "%s%a" init printer x;
  | h::t ->
      fprintf oc "%s%a%s" init printer h sep;
      p_list init printer sep oc t;
;;

let p_type oc t =
  match t with
  | t when t = univ_name -> fprintf oc "%s" t;
  | "?" -> fprintf oc "_";
  | s -> fprintf oc "%s" s;
;;

let rec decompose_lambda e =
  match e with
  | Elam (Evar (v, _), t, b, _) ->
     let bindings, body = decompose_lambda b in
     ((v, t) :: bindings), body
  | Elam _ -> assert false
  | _ -> [], e
;;

let p_binding oc (v, t) =
  fprintf oc "(%s : %a)" v p_type t
;;

let p_id_list oc l = p_list " " (fun oc x -> fprintf oc "%s" x) "" oc l;;

let rec p_expr oc e =
  let poc fmt = fprintf oc fmt in
  match e with
  | Evar (v, _) when Mltoll.is_meta v ->
      poc "%s" (Coqterm.synthesize v);
  | Evar (v, _) ->
      poc "%s" v;
  | Eapp ("=", [e1; e2], _) ->
      poc "(%a = %a)" p_expr e1 p_expr e2;
  | Eapp ("=", l, _) ->
      p_expr oc (eapp ("@eq _", l));
  | Eapp ("$match", e1 :: l, _) ->
      poc "match %a with%a end" p_expr e1 p_cases l;
  | Eapp ("$fix", Elam (Evar (f, _), _, body, _) :: l, _) ->
      let bindings, expr = decompose_lambda body in
      poc "((fix %s%a := %a)%a)" f (p_list " " p_binding "") bindings
          p_expr expr (p_list " " p_expr "") l
  | Eapp ("FOCAL.ifthenelse", [e1; e2; e3], _) ->
      poc "(if %a then %a else %a)" p_expr e1 p_expr e2 p_expr e3;
  | Eapp (f, l, _) ->
      poc "(%s%a)" f p_expr_list l;
  | Enot (e, _) ->
      poc "(~%a)" p_expr e;
  | Eand (e1, e2, _) ->
      poc "(%a/\\%a)" p_expr e1 p_expr e2;
  | Eor (e1, e2, _) ->
      poc "(%a\\/%a)" p_expr e1 p_expr e2;
  | Eimply (e1, e2, _) ->
      poc "(%a->%a)" p_expr e1 p_expr e2;
  | Eequiv (e1, e2, _) ->
      poc "(%a<->%a)" p_expr e1 p_expr e2;
  | Etrue ->
      poc "True";
  | Efalse ->
      poc "False";
  | Eall (Evar (x, _), t, e, _) ->
      poc "(forall %s : %a, %a)" x p_type t p_expr e;
  | Eall _ -> assert false
  | Eex (Evar (x, _), t, e, _) ->
      poc "(exists %s : %a, %a)" x p_type t p_expr e;
  | Eex _ -> assert false
  | Elam (Evar (x, _), t, e, _) ->
      poc "(fun %s : %a => %a)" x p_type t p_expr e;
  | Elam _ -> assert false
  | Emeta _ -> assert false
  | Etau _ -> assert false

and p_expr_list oc l = p_list " " p_expr "" oc l;

and p_cases oc l = p_list " " (p_case []) "" oc l;

and p_case accu oc e =
  match e with
  | Eapp ("$match-case", [Evar (constr, _); body], _) ->
     fprintf oc "| %s%a => %a" constr p_id_list (List.rev accu) p_expr body;
  | Elam (Evar (v, _), _, body, _) ->
     p_case (v :: accu) oc body
  | _ -> assert false
;;

let rec p_nand oc l =
  match l with
  | e :: t -> fprintf oc "%a -> " p_expr e; p_nand oc t;
  | [] -> fprintf oc "False";
;;

let rec p_bound_vars oc l =
  match l with
  | (v, ty) :: t -> fprintf oc " (%s : %a)" v p_type ty; p_bound_vars oc t;
  | [] -> ()
;;

let rec p_forall oc l =
  match l with
  | _ :: _ -> fprintf oc "forall%a, " p_bound_vars l;
  | [] -> ()
;;

let get_goals concl =
  List.filter (fun x -> Coqterm.is_goal x || not (Coqterm.is_mapped x)) concl
;;

let declare_lemma oc name params concl =
  fprintf oc "Lemma %s : %a%a.\n" name p_forall params p_nand (get_goals concl);
;;

let declare_theorem oc name params concl phrases =
  let nconcl =
    match get_goals concl with
    | [ Enot (e, _) ] -> e
    | [] -> efalse
    | _ -> assert false
  in
  fprintf oc "Theorem %s : %a%a.\n" name p_forall params p_expr nconcl;
  fprintf oc "Proof.\n";
  Coqterm.print_use_all oc phrases;
;;

let getname = Coqterm.getname;;

let p_name_list oc l =
  p_list " " (fun oc e -> fprintf oc "%s" (getname e)) "" oc l;
;;

let p_start_lemma oc nvars conc =
  fprintf oc "do %d intro. intros %a.\n" nvars p_name_list conc
;;

let p_start_thm oc conc =
  match get_goals conc with
  | [] -> ()
  | [e] -> fprintf oc "apply NNPP. intro %s.\n" (getname e);
  | _ -> assert false
;;

let p_end oc = fprintf oc "Qed.\n";;

let p_intro oc e =
  fprintf oc "zenon_intro %s; " (getname e);
;;

let p_intros oc l =
  List.iter (p_intro oc) l;
  fprintf oc "idtac";
;;

let p_rev_app oc (f, args) =
  fprintf oc "(%s%a)" f p_expr_list (List.rev args)
;;

let rec p_equal_steps oc f l0 l1 =
  match l0, l1 with
  | _, _ when List.for_all2 Expr.equal l0 l1 ->
      fprintf oc "auto";
      List.length l0
  | e0 :: t0 , e1 :: t1 ->
      let e0nee1 = enot (eapp ("=", [e0; e1])) in
      fprintf oc "apply (zenon_equal_step _ _ %a %a %a %a); [ "
              p_rev_app (f, t0) p_rev_app (f, t1) p_expr e0 p_expr e1;
      let useless = p_equal_steps oc f t0 t1 in
      fprintf oc " | zenon_intro %s ]" (getname e0nee1);
      useless
  | _, _ -> assert false
;;

let apply_alpha oc lem h0 h1 h2 =
  fprintf oc "apply (zenon_%s_s _ _ %s). zenon_intro %s. zenon_intro %s.\n"
             lem (getname h0) (getname h1) (getname h2);
  0
;;

let apply_beta oc lem h0 h1 h2 =
  fprintf oc "apply (zenon_%s_s _ _ %s); [ zenon_intro %s | zenon_intro %s ].\n"
             lem (getname h0) (getname h1) (getname h2);
  0
;;

let apply_beta2 oc lem h0 h1a h1b h2a h2b =
  fprintf oc "apply (zenon_%s_s _ _ %s); \
              [ zenon_intro %s; zenon_intro %s \
                | zenon_intro %s; zenon_intro %s ].\n"
             lem (getname h0) (getname h1a) (getname h1b)
             (getname h2a) (getname h2b);
  0
;;

let p_rule oc r =
  let poc fmt = fprintf oc fmt in
  match r with
  | Rconnect (And, e1, e2) ->
      apply_alpha oc "and" (eand (e1, e2)) e1 e2
  | Rconnect (Or, e1, e2) ->
      apply_beta oc "or" (eor (e1, e2)) e1 e2
  | Rconnect (Imply, e1, e2) ->
      apply_beta oc "imply" (eimply (e1, e2)) (enot e1) e2
  | Rconnect (Equiv, e1, e2) ->
      apply_beta2 oc "equiv" (eequiv (e1, e2)) (enot e1) (enot e2) e1 e2
  | Rnotconnect (And, e1, e2) ->
      apply_beta oc "notand" (enot (eand (e1, e2))) (enot e1) (enot e2)
  | Rnotconnect (Or, e1, e2) ->
      apply_alpha oc "notor" (enot (eor (e1, e2))) (enot e1) (enot e2)
  | Rnotconnect (Imply, e1, e2) ->
      apply_alpha oc "notimply" (enot (eimply (e1, e2))) e1 (enot e2)
  | Rnotconnect (Equiv, e1, e2) ->
      apply_beta2 oc "notequiv" (enot (eequiv (e1, e2)))
                  (enot e1) e2 e1 (enot e2)
  | Rextension ("zenon_inductive_discriminate", [], [conc], []) ->
      poc "discriminate %s.\n" (getname conc);
      0
(*
  | Rextension ("zenon_inductive_match_neq_right", [e1; e2], [conc], hyps) ->
      ...
*)
  | Rextension (name, args, conc, hyps) ->
      poc "apply (%s_s%a%a)" name p_expr_list args p_name_list conc;
      begin match hyps with
      | [] -> poc ".\n";
      | _ -> poc "; [ %a ].\n" (p_list "" p_intros " | ") hyps;
      end;
      0
  | Rnotnot (p as e) ->
      poc "apply %s. zenon_intro %s.\n" (getname (enot (enot e))) (getname e);
      0
  | Rex (Eex (x, _, e, _) as p, v) ->
      let h0 = getname p in
      let h1 = getname (substitute [(x, evar v)] e) in
      poc "elim %s. zenon_intro %s. zenon_intro %s.\n" h0 v h1;
      0
  | Rex _ -> assert false
  | Rnotall (Eall (x, _, e, _) as p, v) ->
      let h0 = getname (enot p) in
      let h1 = getname (enot (substitute [(x, evar v)] e)) in
      poc "apply %s. zenon_intro %s. apply NNPP. zenon_intro %s.\n" h0 v h1;
      0
  | Rnotall _ -> assert false
  | Rall (Eall (x, _, e, _) as p, t) ->
      let h0 = getname p in
      let h1 = getname (substitute [(x, t)] e) in
      poc "generalize (%s %a). zenon_intro %s.\n" h0 p_expr t h1;
      0
  | Rall _ -> assert false
  | Rnotex (Eex (x, _, e, _) as p, t) ->
      let h0 = getname (enot p) in
      let h1 = getname (enot (substitute [(x, t)] e)) in
      poc "apply %s. exists %a. apply NNPP. zenon_intro %s.\n" h0 p_expr t h1;
      0
  | Rnotex _ -> assert false
  | Rlemma (name, args) ->
      let args1 = List.filter (fun x -> not (Mltoll.is_meta x)) args in
      poc "apply (%s%a); trivial.\n" name p_id_list args1;
      0
  | Rcut (e) ->
      let h0 = getname e in
      let h1 = getname (enot e) in
      poc "elim (classic %a); [ zenon_intro %s | zenon_intro %s ].\n"
          p_expr e h0 h1;
      0
  | Raxiom (e) ->
      let h0 = getname e in
      let h1 = getname (enot e) in
      poc "exact (%s %s).\n" h1 h0;
      0
  | Rdefinition (_, s, c, h) ->
      poc "assert (%s : %a). exact %s.\n" (getname h) p_expr h (getname c);
      0
  | Rnotequal ((Eapp (f, l0, _) as e0), (Eapp (g, l1, _) as e1)) ->
      assert (f = g);
      let h0 = getname (enot (eapp ("=", [e0; e1]))) in
      poc "apply (zenon_notequal_s _ _ _ %s); " h0;
      let useless = p_equal_steps oc f (List.rev l0) (List.rev l1) in
      poc ".\n";
      useless
  | Rnotequal _ -> assert false
  | Rpnotp ((Eapp (f, l0, _) as e0), (Enot (Eapp (g, l1, _), _) as e1)) ->
      assert (f = g);
      let f1 = if f = "=" then "@eq _" else f in
      let h0 = getname e0 in
      let h1 = getname e1 in
      poc "apply (zenon_pnotp_s _ _ %s %s); " h0 h1;
      let useless = p_equal_steps oc f1 (List.rev l0) (List.rev l1) in
      poc ".\n";
      useless
  | Rpnotp _ -> assert false
  | Rnoteq e ->
      poc "apply %s. apply refl_equal.\n" (getname (enot (eapp ("=", [e; e]))));
      0
  | Reqsym (e, f) ->
      poc "apply %s. apply sym_equal. exact %s.\n"
          (getname (enot (eapp ("=", [f; e]))))
          (getname (eapp ("=", [e; f])));
      0
  | Rnottrue ->
      poc "exact (%s I).\n" (getname (enot (etrue)));
      0
  | Rfalse ->
      poc "exact %s.\n" (getname efalse);
      0
;;

let rec drop n l =
  match n, l with
  | 0, l -> l
  | n, h::t -> assert (n > 0); drop (n-1) t
  | _, _ -> assert false
;;

let rec p_tree oc proof =
  let useless = p_rule oc proof.rule in
  List.iter (p_tree oc) (drop useless proof.hyps);
;;

let p_script_lemma oc nvars proof =
  p_start_lemma oc nvars (get_goals proof.conc);
  p_tree oc proof;
  p_end oc;
;;

let p_script_thm oc proof =
  p_start_thm oc (get_goals proof.conc);
  p_tree oc proof;
  p_end oc;
;;

let notmeta (v, _) = not (Mltoll.is_meta v);;

let rec p_lemmas oc phrases l =
  match l with
  | [] -> assert false
  | [thm] ->
      let params = List.filter notmeta thm.params in
      declare_theorem oc thm.name params thm.proof.conc phrases;
      p_script_thm oc thm.proof;
  | lem :: t ->
      let params = List.filter notmeta lem.params in
      declare_lemma oc lem.name params lem.proof.conc;
      p_script_lemma oc (List.length params) lem.proof;
      p_lemmas oc phrases t;
;;

let output oc phrases ppphrases llp =
  try
    Coqterm.init_mapping phrases;
    Coqterm.init_inductive ppphrases;
    if !Globals.ctx_flag then Coqterm.declare_context oc phrases;
    if not !Globals.quiet_flag then fprintf oc "(* BEGIN-PROOF *)\n";
    p_lemmas oc phrases llp;
    if not !Globals.quiet_flag then fprintf oc "(* END-PROOF *)\n";
    !Coqterm.constants_used
  with
  | Coqterm.Cannot_infer ty ->
      let msg = sprintf "cannot infer a value for a variable of type %s" ty in
      Error.err msg;
      raise Error.Abort
;;
