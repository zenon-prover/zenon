(*  Copyright 2004 INRIA  *)
Version.add "$Id: lltocoq.ml,v 1.23 2005-11-05 11:13:17 doligez Exp $";;

open Printf

open Expr
open Llproof

let debug = ref false

(********************)
(* Stream utilities *)
(********************)

let str s = [< 's >]
let ints s = [< '(string_of_int s) >]
let coqend = [< '".\n" >]
let coqp s = [< 's; coqend >]
let parth s = [< '"("; s; '")" >]

let flush_strm stm outc =
  try
    while true do
      output_string outc (Stream.next stm)
    done
  with Stream.Failure -> flush outc

let ppvernac_dir outc s = flush_strm s outc

(******************************)
(* Translation expr to constr *)
(******************************)

let constr_of_type t =
  match t with
  | "" -> [< '"z'U" >]
  | "?" -> [< '"_" >]
  | s -> [< 's >]
;;

let rec constr_of_expr = function
  | Evar (v, _) when Mltoll.is_meta v -> [< 'Coqterm.synthesize v >]
  | Evar (v, _) -> [< 'v >]
  | Eapp ("=", [e1; e2], _) ->
    parth [< constr_of_expr e1; str " = "; constr_of_expr e2 >]
  | Eapp ("=", [], _) -> [< str "(eq (A:=_))" >]
  | Eapp ("=", l, _) -> constr_of_expr (eapp ("eq", l))
  | Eapp (f, l, _) ->
    parth [< 'f; List.fold_left
                 (fun s e -> [< s; str " "; (constr_of_expr e) >]) [< >] l >]
  | Enot (e, _) -> [< str "~"; constr_of_expr e >]
  | Eand (e1, e2, _) ->
    parth [< constr_of_expr e1; str "/\\"; constr_of_expr e2 >]
  | Eor (e1, e2, _) ->
    parth [< constr_of_expr e1; str "\\/"; constr_of_expr e2 >]
  | Eimply (e1, e2, _) ->
    parth [< constr_of_expr e1; str "->"; constr_of_expr e2 >]
  | Eequiv (e1, e2, _) ->
    parth [< constr_of_expr e1; str "<->"; constr_of_expr e2 >]
  | Etrue -> [< str "True" >]
  | Efalse -> [< str "False" >]
  | Eall (Evar (x, _), t, e, _, _) ->
    parth [< str "forall "; str x; str ":"; constr_of_type t;
             str ","; constr_of_expr e >]
  | Eex (Evar (x, _), t, e, _, _) ->
    parth [< str "exists "; str x; str ":"; constr_of_type t;
             str ","; constr_of_expr e >]
  | _ -> if !debug then [< str "..." >] else assert false
;;

let parth_constr_of_expr e =
  match e with
  | Enot _ -> parth (constr_of_expr e)
  | _ -> constr_of_expr e
;;

(*********************)
(* Type declarations *)
(*********************)

let rec make_prod = function
  | [] -> [< str " False" >]
  | e :: l -> [< constr_of_expr e; str " -> "; make_prod l >]
;;

(************************)
(* Coq proof generation *)
(************************)

let mapping = (Hashtbl.create 97 : (int, string) Hashtbl.t);;

let rec make_mapping phrases =
  let f phr =
    match phr with
    | Phrase.Hyp ("z'goal", _, _) -> ()
    | Phrase.Hyp (n, e, _) -> Hashtbl.add mapping (Index.get_number e) n
    | Phrase.Def _ -> ()
    | Phrase.Sig _ -> ()
  in
  List.iter f phrases;
;;

let rec make_params = function
  | [] -> [< >]
  | (x, typ) :: l -> [< str "forall "; str x; str " : "; constr_of_type typ;
                        str ", "; make_params l >]

let get_goals concl =
  let not_global_hyp e = not (Hashtbl.mem mapping (Index.get_number e)) in
  List.filter not_global_hyp concl
;;

let declare_lemma ppvernac name params concl =
  ppvernac [< str "Lemma "; str name; str " : "; make_params params;
              make_prod (get_goals concl); coqend >]
;;

let declare_theorem ppvernac name params concl =
  let prod_concl =
    match get_goals concl with
    | [ Enot (e, _) ] -> [< constr_of_expr e >]
    | [] -> [< str " False " >]
    | _ -> assert false
  in
  ppvernac [< str "Lemma "; str name; str " : "; make_params params;
              prod_concl; coqend >]

let rec gen_name e =
  let n = Index.get_number e in
  try
    let name = Hashtbl.find mapping n in
    [< str " "; str name >]
  with Not_found -> [< str " ZH"; ints n >]
;;

let proof_init ppvernac nfv conc is_lemma =
  let lnam = List.fold_left (fun s e -> [< s; gen_name e >]) [< >] conc in
  if is_lemma then
    ppvernac [< str "do "; ints nfv; str " intro; intros"; lnam; coqend >]
  else
    let intros =
      match get_goals conc with
      | [ e ] -> [< str " apply NNPP; intros"; gen_name e; coqend >]
      | [] -> [< >]
      | _ -> assert false
    in
    ppvernac [< intros >]
;;

let proof_end ppvernac =
  ppvernac [< coqp "Qed" >];
;;

let inst_name t = function
  | Eex (x, _, e, _, _) -> let ti = enot (substitute [ x, t ] e) in gen_name ti
  | Eall (x, _, e, _, _) -> let ti = substitute [ x, t ] e in gen_name ti
  | _ -> assert false
;;

let rec list_of f l sep =
  match l with
  | [] -> [< >]
  | [h] -> [< f h >]
  | h::t -> [< f h; str sep; list_of f t sep >]
;;

let rec init_list_of f l sep =
  match l with
  | [] -> [< >]
  | h::t -> [< str sep; f h; init_list_of f t sep >]
;;

let rec term_list_of f l sep =
  match l with
  | [] -> [< >]
  | h::t -> [< f h; str sep; term_list_of f t sep >]
;;

let make_intros l =
  match l with
  | [] -> [< str "idtac" >]
  | _ -> [< str "intros"; list_of (fun e -> gen_name e) l "" >]
;;

let make_exact e = [< str "exact"; gen_name e >];;

let rec make_app f l =
  match l with
  | [] -> [< str f >]
  | h::t -> [< make_app f t; str " "; constr_of_expr h >]
;;

let rec apply_equal_steps f l0 l1 =
  match l0, l1 with
  | _, _ when List.for_all2 Expr.equal l0 l1 -> [< str "auto" >], List.length l0
  | h0 :: t0 , h1 :: t1 ->
      let (steps, useless) = apply_equal_steps f t0 t1 in
      [< str "apply (zenon_equal_step _ _ (";
         make_app f t0; str ") (";
         make_app f t1; str ") "; constr_of_expr h0; str " ";
         constr_of_expr h1; str "); [ "; steps;
         str " | cintro"; gen_name (enot (eapp ("=", [h0; h1]))); str " ]" >],
      useless
  | _, _ -> assert false
;;

let proof_rule ppvernac = function
  | Rconnect (And, e1, e2) ->
    let hyp0 = gen_name (eand (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2 in
    if !debug then ppvernac [< '"(* connect(And) *)\n" >];
    ppvernac [< str "elim"; hyp0; str "; cintro"; hyp1;
                str "; cintro"; hyp2; coqend >];
    0
  | Rconnect (Or, e1, e2) ->
    let hyp0 = gen_name (eor (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2 in
    if !debug then ppvernac [< '"(* connect(Or) *)\n" >];
    ppvernac [< str "elim"; hyp0; str ";[ cintro"; hyp1; str " | cintro"; hyp2;
                coqp " ]" >];
    0
  | Rconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (eimply (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1) in
    if !debug then ppvernac [< '"(* connect(Imply) *)\n" >];
    ppvernac [< str "cut "; parth (constr_of_expr (enot e1)); str "; [ cintro";
                hyp3; str " | red; cintro"; hyp1; str "; generalize (";
                hyp0; hyp1; str "); cintro"; hyp2; coqp " ]" >];
    0
  | Rconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (eequiv (e1, e2))
    and hyp1 = gen_name (eimply (e1, e2))
    and hyp2 = gen_name (eimply (e2, e1))
    and hyp3 = gen_name e1
    and hyp4 = gen_name e2
    and hyp5 = gen_name (enot e1)
    and hyp6 = gen_name (enot e2) in
    if !debug then ppvernac [< '"(* connect(Equiv) *)\n" >];
    ppvernac [< str "unfold iff at 1 in"; hyp0; str "; elim"; hyp0;
                str "; cintro"; hyp1; str "; cintro"; hyp2; str "; cut ";
                parth (constr_of_expr (enot e1)); str "; [ cintro";
                hyp5; str "; cut "; parth (constr_of_expr e2);
                str "; [ auto | apply NNPP; red; cintro"; hyp6;
                str "; clear"; hyp1; hyp2; str " ] | red; cintro"; hyp3;
                str "; generalize ("; hyp1; hyp3; str "); cintro"; hyp4;
                str "; clear"; hyp1; hyp2; coqp " ]" >];
    0
  | Rnotconnect (And, e1, e2) ->
    let hyp0 = gen_name (enot (eand (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< '"(* notconnect(And) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; split; apply NNPP; [ cintro";
                hyp1; str " | cintro"; hyp2; coqp " ]" >];
    0
  | Rnotconnect (Or, e1, e2) ->
    let hyp0 = gen_name (enot (eor (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< '"(* notconnect(Or) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; left; apply NNPP; red; cintro";
                hyp1; str "; apply"; hyp0;
                str "; right; apply NNPP; red; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (enot (eimply (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< '"(* notconnect(Imply) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; cintro"; hyp1;
                str "; apply NNPP; red; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (enot (eequiv (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1)
    and hyp4 = gen_name (enot e2) in
    if !debug then ppvernac [< '"(* notconnect(Equiv) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; apply iff_sym; split; [ cintro";
                hyp2; str "; apply NNPP; red; cintro"; hyp3;
                str " | cintro"; hyp1; str "; apply NNPP; red; cintro";
                hyp4; coqp " ] " >];
    0
  | Rnotnot (p as e) ->
    let hyp0 = gen_name (enot (enot e))
    and hyp1 = gen_name p in
    if !debug then ppvernac [< '"(* not(not) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; clear"; hyp0;
                str "; cintro"; hyp1; coqend >];
    0
  | Rnotall (Eall (x, _, e, _, _) as t, z) ->
    let hyp0 = gen_name (enot t)
    and hyp1 = gen_name (enot (substitute [(x, evar z)] e)) in
    if !debug then ppvernac [< '"(* not(all) *)\n" >];
    ppvernac [< str "apply"; hyp0; str "; cintro "; str z;
                str "; apply NNPP; red; cintro"; hyp1; coqend >];
    0
  | Rnotall _ -> assert false
  | Rnotex (p, t) ->
    let hyp = gen_name (enot p) in
    begin
      if !debug then ppvernac [< '"(* not(ex) *)\n" >];
      ppvernac [< str "apply"; hyp; coqend >];
      ppvernac [< str "exists "; constr_of_expr t;
                  str "; apply NNPP; red; cintro"; inst_name t p; coqend >]
    end;
    0
  | Rall (p, t) ->
    let hyp = gen_name p in
    begin
      if !debug then ppvernac [< '"(* all *)\n" >];
      ppvernac [< str "generalize ("; hyp; str " "; constr_of_expr t;
                  str "); cintro"; inst_name t p; coqend >]
    end;
    0
  | Rex (Eex (x, _, e, _, _) as t, z) ->
    let hyp0 = gen_name t
    and hyp1 = gen_name (substitute [(x, evar z)] e) in
    if !debug then ppvernac [< '"(* ex *)\n" >];
    ppvernac [< str "elim"; hyp0;
                str "; cintro "; str z; str "; cintro"; hyp1; coqend >];
    0
  | Rex _ -> assert false
  | Rlemma (n, args) ->
    if !debug then ppvernac [< '"(* lemma *)\n" >];
    let newargs = List.filter (fun x -> not (Mltoll.is_meta x)) args in
    let f s e = [< s; str " "; str e >] in
    ppvernac [< str "intros; apply ("; str n;
                List.fold_left f [< >] newargs;
                str ")"; coqp "; trivial" >];
    0
  | Rcut (e) ->
    if !debug then ppvernac [< '"(* cut *)\n" >];
    ppvernac [< str "cut "; parth (constr_of_expr e);
                str "; [ cintro "; gen_name e;
                str " | apply NNPP; cintro "; gen_name (enot e);
                coqp " ]" >];
    0
  | Raxiom (e) ->
    if !debug then ppvernac [< '"(* axiom *)\n" >];
    ppvernac [< str "exact ("; gen_name (enot e); str " "; gen_name e;
                coqp ")" >];
    0
  | Rextension (name, args, conc, hyps) ->
    ppvernac [< str "apply ("; str name;
                init_list_of parth_constr_of_expr args " ";
                str "); ["; term_list_of make_intros hyps " | ";
                list_of make_exact conc " | "; coqp "]" >];
    0
  | Rdefinition (c, h) ->
    if !debug then ppvernac [< '"(* definition *)\n" >];
    ppvernac [< str "pose ("; gen_name h; str " := "; gen_name c; coqp ")" >];
    0
  | Rnotequal ((Eapp (f, l0, _) as e0), (Eapp (g, l1, _) as e1)) ->
    assert (f = g);
    let hyp0 = gen_name (enot (eapp ("=", [e0; e1]))) in
    let (steps, useless) = apply_equal_steps f (List.rev l0) (List.rev l1) in
    ppvernac [< str "apply (zenon_notequal_s _ _ _"; hyp0; str "); ";
                steps; coqend >];
    useless
  | Rnotequal _ -> assert false
  | Rpnotp ((Eapp (f, l0, _) as h0), (Enot (Eapp (g, l1, _), _) as h1)) ->
    assert (f = g);
    let fg = if f = "=" then "eq (A:=_)" else f in
    let hyp0 = gen_name h0 in
    let hyp1 = gen_name h1 in
    let (steps, useless) = apply_equal_steps fg (List.rev l0) (List.rev l1) in
    ppvernac [< str "apply (zenon_pnotp_s _ _"; hyp0; hyp1; str "); ";
                steps; coqend >];
    useless
  | Rpnotp _ -> assert false

  | Rnoteq e ->
      let hyp0 = gen_name (enot (eapp ("=", [e; e]))) in
      ppvernac [< str "apply"; hyp0; str "; auto"; coqend >];
      0
  | Rnottrue ->
      let hyp0 = gen_name (enot (etrue)) in
      ppvernac [< str "apply"; hyp0; str "; auto"; coqend >];
      0
  | Rfalse ->
      let hyp0 = gen_name (efalse) in
      ppvernac [< str "apply"; hyp0; coqend >];
      0
;;

(* experimental version *)
let proof_rule_short ppvernac = function
  | Rconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (eimply (e1, e2))
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1) in
    ppvernac [< str "apply (zenon_imply_s _ _"; hyp0; str "); [ cintro"; hyp3;
                str " | cintro"; hyp2; coqp " ]" >];
    0
  | Rconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (eequiv (e1, e2))
    and hyp3 = gen_name e1
    and hyp4 = gen_name e2
    and hyp5 = gen_name (enot e1)
    and hyp6 = gen_name (enot e2) in
    ppvernac [< str "apply (zenon_equiv_s _ _"; hyp0; str "); [ cintro"; hyp5;
                str "; cintro"; hyp6; str " | cintro"; hyp3; str "; cintro";
                hyp4; coqp " ]" >];
    0
  | Rnotconnect (And, e1, e2) ->
    let hyp0 = gen_name (enot (eand (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    ppvernac [< str "apply (zenon_notand_s _ _"; hyp0; str "); [ cintro"; hyp1;
                 str " | cintro "; hyp2; coqp " ]" >];
    0
  | Rnotconnect (Or, e1, e2) ->
    let hyp0 = gen_name (enot (eor (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    ppvernac [< str "apply (zenon_notor_s _ _"; hyp0; str "); cintro"; hyp1;
                str "; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (enot (eimply (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name (enot e2) in
    ppvernac [< str "apply (zenon_notimply_s _ _"; hyp0; str "); cintro"; hyp1;
                str "; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (enot (eequiv (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1)
    and hyp4 = gen_name (enot e2) in
    ppvernac [< str "apply (zenon_notequiv_s _ _"; hyp0;
                str "); [ cintro"; hyp3;
                str "; cintro"; hyp2; str " | cintro"; hyp1;
                str "; cintro"; hyp4; coqp " ]" >];
    0
  | Rextension (name, args, conc, hyps) ->
      let wildcard = function _ -> [< str "_" >] in
      ppvernac [< str "apply ("; str name; str "_s";
                  init_list_of wildcard args " "; list_of gen_name conc "";
                  str "); ["; list_of make_intros hyps " | "; coqp "]" >];
      0
  | x -> proof_rule ppvernac x
;;

let rec drop n l =
  match n, l with
  | 0, l -> l
  | n, h::t -> assert (n > 0); drop (n-1) t
  | _, _ -> assert false
;;

let rec proof_build ppvernac pft =
  let useless_hyps =
    if !Globals.short_flag then
      proof_rule_short ppvernac pft.rule
    else
      proof_rule ppvernac pft.rule
  in
  List.iter (proof_build ppvernac) (drop useless_hyps pft.hyps);
;;

let proof_script ppvernac n pft is_lemma =
  begin
    proof_init ppvernac n (get_goals pft.conc) is_lemma;
    proof_build ppvernac pft;
    proof_end ppvernac
  end

let rec proof_lem ppvernac lems =
  match lems with
  | [] -> ()
  | lem :: rest ->
  let name = lem.name in
  let concl = lem.proof.conc in
  let nometa (v, t) = not (Mltoll.is_meta v) in
  let params = List.filter nometa lem.params in
  let pft = lem.proof in
  if rest = [] then begin
    declare_theorem ppvernac name params concl;
    proof_script ppvernac (List.length params) pft false;
  end else begin
    declare_lemma ppvernac name params concl;
    proof_script ppvernac (List.length params) pft true;
  end;
  proof_lem ppvernac rest
;;

(***************)
(* Translation *)
(***************)

let produce_proof oc phrases llp =
  make_mapping phrases;
  let ppvernac = ppvernac_dir oc in
  if !Globals.ctx_flag then Coqterm.declare_context oc phrases;
  if not !Globals.quiet_flag then ppvernac [< '"(* BEGIN-PROOF *)\n" >];
  proof_lem ppvernac llp;
  if not !Globals.quiet_flag then ppvernac [< '"(* END-PROOF *)\n" >];
;;
