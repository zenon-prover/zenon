(*  Copyright 2004 INRIA  *)
Version.add "$Id: lltocoq.ml,v 1.20 2005-04-15 14:08:20 doligez Exp $";;

(**********************************************************************)
(* Some preliminary remarks:                                          *)
(*   - we use Coq V8 and higher (V7 is not supported)                 *)
(*   - there are two translations:                                    *)
(*     (1) a direct translation (with a raw pretty-print)             *)
(*     (2) a translation using Coq (which parses and pretty-prints)   *)
(*     (1) is faster than (2) whereas (2) is safer and nicer than (1) *)
(*   - we use "Unixies" but all of them are supported under Windows   *)
(**********************************************************************)

open Expr
open Llproof

let debug = ref false

(********************)
(* Stream utilities *)
(********************)

let nwl = [< '"\n" >]
let str s = [< 's >]
let strnl s = [< (str s); nwl >]
let ints s = [< str (string_of_int s) >]
let camlend = [< strnl ";;" >]
let coqend = [< strnl "." >]
let camlp s = [< (str s); camlend >]
let coqp s = [< (str s); coqend >]
let parth s = [< '"("; s; '")" >]
let thenc = [< str "; " >]

let flush_strm stm outc =
  try
    while true do
      output_string outc (Stream.next stm)
    done
  with | Stream.Failure -> flush outc

(*************************************************)
(* Pretty-print functions (with and without Coq) *)
(*************************************************)

let read_msg inc =
  try while true do ignore (input_line inc) done
  with Sys_blocked_io -> ()

let ppvernac_coq (inc, outc) s =
  begin
    flush_strm [< str "ppvernac (parse_vernac \""; s; camlp "\")" >] outc;
    read_msg inc
  end

let ppvernac_dir outc s = flush_strm s outc

(******************************)
(* Translation expr to constr *)
(******************************)

let rec constr_of_expr = function
  | Evar (v, _) -> [< 'v >]
  | Eapp ("=", [e1; e2], _) ->
    parth [< constr_of_expr e1; str " = "; constr_of_expr e2 >]
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
  | Eall (Evar (x, _), t, e, _) ->
    parth [< str "forall "; str x; str " : "; if t <> "" then [< str t >]
             else [< str "U" >]; str ","; constr_of_expr e >]
  | Eex (Evar (x, _), t, e, _) ->
    parth [< str "exists "; str x; str " : "; if t <> "" then [< str t >]
             else [< str "U" >]; str ","; constr_of_expr e >]
(*
  | Eall (Evar (x, _), t, e, _) ->
    parth [< str "forall "; str x; if t <> "" then [< str ":"; str t >]
             else [< >]; str ","; constr_of_expr e >]
  | Eex (Evar (x, _), t, e, _) ->
    parth [< str "exists "; str x; if t <> "" then [< str ":"; str t >]
             else [< >]; str ","; constr_of_expr e >]
*)
  | _ -> if !debug then [< str "..." >] else assert false

let parth_constr_of_expr e =
  match e with
  | Enot _ -> parth (constr_of_expr e)
  | _ -> constr_of_expr e
;;

(***********************)
(* Require's & Tactics *)
(***********************)

let requires = [ "zenon8" ]

let make_require lib = [< str "Require Import "; coqp lib >]

let require ppvernac =
  let req = List.fold_left (fun s e -> [< s; make_require e >])
                           [< >] requires in
  ppvernac req

let contract_intro =
  [< str "Ltac cintro id := intro id || let nid := fresh in (intro nid; ";
     coqp "clear nid)" >]

let tactic ppvernac = ppvernac contract_intro

(*********************)
(* Type declarations *)
(*********************)

let rec list_types = function
  | [ ] -> [< >]
  | e :: l -> [< str e; str " "; list_types l >]

let rec make_parameters = function
  | [] -> [< >]
  | e :: l -> [< str "forall "; str e; str ", "; make_parameters l >]

let rec make_prod = function
  | [ t ] -> [< constr_of_expr t; str " -> False" >]
  | e :: l -> [< constr_of_expr e; str " -> "; make_prod l >]
  | _ -> assert false

let declare_types ppvernac types =
  let lst = list_types types in
  ppvernac [< if (List.length types) = 1 then [< str "Parameter " >]
              else [< str "Parameters " >]; lst; coqp ": Set" >]

let normal f = List.fold_left (fun a e -> if f e a then a else a @ [e]) []

let declare_lem chns lem =
  let concl = lem.proof.conc in
  let typ = List.flatten (List.map type_list concl)
  and fvr = List.flatten (List.map free_var concl) in
  if List.exists (fun (_, (s, a)) -> s = false && a = 0) fvr then "U" :: typ
  else typ

let declare chns llp =
  let types = normal (fun e l -> List.mem e l)
              (List.fold_left (fun a e -> a @ (declare_lem chns e)) [] llp) in
  if types <> [] then declare_types chns types

(************************)
(* Coq proof generation *)
(************************)

let mapping = (Hashtbl.create 97 : (int, string) Hashtbl.t);;

let rec make_mapping phrases =
  let f phr =
    match phr with
    | Phrase.Hyp ("_Zgoal", _, _) -> ()
    | Phrase.Hyp (n, e, _) -> Hashtbl.add mapping (Index.get_number e) n
    | Phrase.Def _ -> ()
  in
  List.iter f phrases;
;;

let rec make_params = function
  | [] -> [< >]
  | (x, typ) :: l -> [< str "forall "; str x; str " : "; if typ = "" then
                        str "U" else str typ; str ", "; make_params l >]

let rec make_type atom sort arity =
  if arity = 0 then if sort then [< str "Prop" >]
                    else if atom then [< str "U" >] else [< str "_" >]
  else [< str "_ -> "; make_type false sort (arity - 1) >]

let rec make_fvar = function
  | [] -> [< >]
  | (n, (s, a)) :: l -> [< str "forall "; str n; str " : "; make_type true s a;
                           str ", "; make_fvar l >]

let get_goals concl =
  let not_global_hyp e = not (Hashtbl.mem mapping (Index.get_number e)) in
  List.filter not_global_hyp concl
;;

let declare_lemma ppvernac name params fvar concl =
  ppvernac [< str "Lemma "; str name; str " : "; make_params params;
              make_fvar fvar; make_prod (get_goals concl); coqend >]

let declare_theorem ppvernac name params fvar concl =
  let prod_concl =
    if !Globals.ctx_flag then
      make_prod concl
    else
      match get_goals concl with
      | [ Enot (e, _) ] -> [< constr_of_expr e >]
      | [] -> [< str " False " >]
      | _ -> assert false
  in
  ppvernac [< str "Lemma "; str name; str " : "; make_params params;
              make_fvar fvar; prod_concl; coqend >]

let rec gen_name e =
  let n = Index.get_number e in
  try
    let name = Hashtbl.find mapping n in
      Watch.use_hyp name;
      [< str " "; str name >]
  with Not_found -> [< str " ZH"; ints (Index.get_number e) >]
;;

let rec print_all_names ppvernac n =
  try
    let form = constr_of_expr (Index.get_formula n) in
    begin try
      let name = Hashtbl.find mapping n in
      ppvernac [< str name; str " "; form; nwl >]
    with Not_found ->
      ppvernac [< str "ZH"; ints n; str " "; form; nwl >]
    end;
    print_all_names ppvernac (n+1);
  with Not_found -> ()
;;

let proof_init ppvernac nfv conc is_lemma =
  let lnam = List.fold_left (fun s e -> [< s; gen_name e >]) [< >] conc in
  if !Globals.ctx_flag || is_lemma then
    ppvernac [< str "do "; ints nfv; str " intro; intros"; lnam; coqend >]
  else
   let intros =
     match get_goals conc with
     | [ e ] -> [< str " apply NNPP; intros "; gen_name e; coqend >]
     | [] -> [< >]
     | _ -> assert false
   in
   ppvernac [< intros >]
;;

let proof_end ppvernac =
  ppvernac [< coqp "Qed" >];
  if !debug then begin
    ppvernac [< strnl "(*" >];
    print_all_names ppvernac 0;
    ppvernac [< strnl "*)" >];
  end

let inst_var = ref []
let reset_var () = inst_var := []

let get_type = function
  | Eex (_, typ, _, _) | Eall (_, typ, _, _) -> if typ = "" then "U" else typ
  | _ -> assert false

let declare_inst ppvernac typ = function
  | Evar (x, _) when String.length x > 2 && (String.sub x 0 2) = "_Z" &&
                     not(List.mem x !inst_var) ->
    begin
      inst_var := x :: !inst_var;
      ppvernac [< str "Parameter "; str x; str " : "; coqp typ >]
    end
  | _ -> ()

let inst_name t = function
  | Eex (x, _, e, _) -> let ti = enot (substitute [ x, t ] e) in gen_name ti
  | Eall (x, _, e, _) -> let ti = substitute [ x, t ] e in gen_name ti
  | _ -> assert false

let rec list_of f l term =
  match l with
  | [] -> [< >]
  | [h] -> [< f h >]
  | h::t -> [< f h; str term; list_of f t term >]
;;

let wildcard _ = [< str "_" >];;

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
    if !debug then ppvernac [< strnl "(* connect(And) *)" >];
    ppvernac [< str "elim"; hyp0; thenc; str "cintro"; hyp1; thenc;
                str "cintro"; hyp2; coqend >];
    0
  | Rconnect (Or, e1, e2) ->
    let hyp0 = gen_name (eor (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2 in
    if !debug then ppvernac [< strnl "(* connect(Or) *)" >];
    ppvernac [< str "elim"; hyp0; str ";[ cintro"; hyp1; str " | cintro"; hyp2;
                coqp " ]" >];
    0
  | Rconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (eimply (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1) in
    if !debug then ppvernac [< strnl "(* connect(Imply) *)" >];
    ppvernac [< str "cut "; parth (constr_of_expr (enot e1)); str "; [ cintro";
                hyp3; str " | red; cintro"; hyp1; thenc; str "generalize (";
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
    if !debug then ppvernac [< strnl "(* connect(Equiv) *)" >];
    ppvernac [< str "unfold iff at 1 in"; hyp0; thenc; str "elim"; hyp0; thenc;
                str "cintro"; hyp1; thenc; str "cintro"; hyp2; thenc;
                str "cut "; parth (constr_of_expr (enot e1)); str "; [ cintro";
                hyp5; thenc; str "cut "; parth (constr_of_expr e2);
                str "; [ auto | apply NNPP; red; cintro"; hyp6; thenc;
                str "clear"; hyp1; hyp2; str " ] | red; cintro"; hyp3; thenc;
                str "generalize ("; hyp1; hyp3; str "); cintro"; hyp4; thenc;
                str "clear"; hyp1; hyp2; coqp " ]" >];
    0
  | Rnotconnect (And, e1, e2) ->
    let hyp0 = gen_name (enot (eand (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< strnl "(* notconnect(And) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "split; apply NNPP; [ cintro";
                hyp1; str " | cintro"; hyp2; coqp " ]" >];
    0
  | Rnotconnect (Or, e1, e2) ->
    let hyp0 = gen_name (enot (eor (e1, e2)))
    and hyp1 = gen_name (enot e1)
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< strnl "(* notconnect(Or) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "left; apply NNPP; red; cintro";
                hyp1; thenc; str "apply"; hyp0; thenc;
                str "right; apply NNPP; red; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Imply, e1, e2) ->
    let hyp0 = gen_name (enot (eimply (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name (enot e2) in
    if !debug then ppvernac [< strnl "(* notconnect(Imply) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "cintro"; hyp1; thenc;
                str "apply NNPP; red; cintro"; hyp2; coqend >];
    0
  | Rnotconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (enot (eequiv (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1)
    and hyp4 = gen_name (enot e2) in
    if !debug then ppvernac [< strnl "(* notconnect(Equiv) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "apply iff_sym; split; [ cintro";
                hyp2; thenc; str "apply NNPP; red; cintro"; hyp3;
                str " | cintro"; hyp1; thenc; str "apply NNPP; red; cintro";
                hyp4; coqp " ] " >];
    0
  | Rnotnot (p as e) ->
    let hyp0 = gen_name (enot (enot e))
    and hyp1 = gen_name p in
    if !debug then ppvernac [< strnl "(* not(not) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "clear"; hyp0; thenc;
                str "intro"; hyp1; coqend >];
    0
  | Rnotall (Eall (x, _, e, _) as t, z) ->
    let hyp0 = gen_name (enot t)
    and hyp1 = gen_name (enot (substitute [(x, evar z)] e)) in
    if !debug then ppvernac [< strnl "(* not(all) *)" >];
    ppvernac [< str "apply"; hyp0; thenc; str "intro "; str z; thenc;
                str "apply NNPP; red; cintro"; hyp1; coqend >];
    0
  | Rnotall _ -> assert false
  | Rnotex (p, t) ->
    let hyp = gen_name (enot p) in
    begin
      if !debug then ppvernac [< strnl "(* not(ex) *)" >];
      ppvernac [< str "apply"; hyp; coqend >];
      declare_inst ppvernac (get_type p) t;
      ppvernac [< str "exists "; constr_of_expr t; thenc;
                  str "apply NNPP; red; intro"; inst_name t p; coqend >]
    end;
    0
  | Rall (p, t) ->
    let hyp = gen_name p in
    begin
      if !debug then ppvernac [< strnl "(* all *)" >];
      declare_inst ppvernac (get_type p) t;
      ppvernac [< str "generalize ("; hyp; str " "; constr_of_expr t;
                  str "); cintro"; inst_name t p; coqend >]
    end;
    0
  | Rex (Eex (x, _, e, _) as t, z) ->
    let hyp0 = gen_name t
    and hyp1 = gen_name (substitute [(x, evar z)] e) in
    if !debug then ppvernac [< strnl "(* ex *)" >];
    ppvernac [< str "elim"; hyp0; thenc;
                str "cintro "; str z; thenc; str "cintro"; hyp1; coqend >];
    0
  | Rex _ -> assert false
  | Rlemma (n, args) ->
    if !debug then ppvernac [< strnl "(* lemma *)" >];
    ppvernac [< str "intros; eapply "; if args = [] then str n else
                [< List.fold_left (fun s e -> [< s; str " "; str e >])
                [< str "("; str n >] args; str ")" >]; thenc; coqp "eauto" >];
    0
  | Rcut (e) ->
    if !debug then ppvernac [< strnl "(* cut *)" >];
    ppvernac [< str "cut "; parth (constr_of_expr e);
                str "; [ cintro "; gen_name e;
                str " | apply NNPP; cintro "; gen_name (enot e);
                coqp " ]" >];
    0
  | Raxiom (e) ->
    if !debug then ppvernac [< strnl "(* axiom *)" >];
    ppvernac [< str "exact ("; gen_name (enot e); str " "; gen_name e;
                coqp ")" >];
    0
  | Rextension (name, args, conc, hyps) ->
    ppvernac [< str "apply ("; str name; str " ";
                list_of parth_constr_of_expr args " ";
                str "); ["; list_of make_intros hyps " | ";
                str " | "; list_of make_exact conc " | "; coqp "]" >];
    0
  | Rdefinition (c, h) ->
    if !debug then ppvernac [< strnl "(* definition *)" >];
    ppvernac [< str "pose ("; gen_name h; str " := "; gen_name c; coqp ")" >];
    0
  | Requalnotequal (t, u, v, w) ->
    let hyp0 = gen_name (eapp ("=", [t; u])) in
    let hyp1 = gen_name (enot (eapp ("=", [v; w]))) in
    let hyp2 = gen_name (enot (eapp ("=", [t; v]))) in
    let hyp3 = gen_name (enot (eapp ("=", [u; v]))) in
    let hyp4 = gen_name (enot (eapp ("=", [u; w]))) in
    let hyp5 = gen_name (enot (eapp ("=", [t; w]))) in
    ppvernac [< str "apply (zenon_equalnotequal_s _ _ _ _ _"; hyp0; hyp1;
                str "); [ cintro"; hyp2; str "; cintro"; hyp3;
                str " | cintro"; hyp4; str "; cintro"; hyp5; coqp " ]" >];
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
    let hyp0 = gen_name h0 in
    let hyp1 = gen_name h1 in
    let (steps, useless) = apply_equal_steps f (List.rev l0) (List.rev l1) in
    ppvernac [< str "apply (zenon_pnotp_s _ _"; hyp0; hyp1; str "); ";
                steps; coqend >];
    useless
  | Rpnotp _ -> assert false

  | Rnoteq _ | Rnottrue | Rfalse -> ppvernac [< coqp "auto" >]; 0

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
    ppvernac [< str "apply ("; str name; str "_s ";
                list_of wildcard args " "; list_of gen_name conc " ";
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
  let name = lem.name
  and concl = lem.proof.conc
  and params = lem.params
  and pft = lem.proof in
  let fvccl =
    if !Globals.ctx_flag then
      normal (fun (e, _) l -> List.mem_assoc e l)
             (List.flatten (List.map free_var concl))
    else List.map (fun (x, _) -> (x, (false, 0))) params
  in
  let fvccl1 = List.filter (fun (e, _) -> e <> "=") fvccl in
  let fvar = List.filter (fun (e, _) -> not (List.mem_assoc e params)) fvccl1 in
  if rest = [] then begin
    declare_theorem ppvernac name params fvar concl;
    proof_script ppvernac (List.length fvccl1) pft false;
  end else begin
    declare_lemma ppvernac name params fvar concl;
    proof_script ppvernac (List.length fvccl1) pft true;
  end;
  proof_lem ppvernac rest

let proof ppvernac lems =
  reset_var ();
  if not !Globals.quiet_flag then ppvernac [< strnl "(* BEGIN-PROOF *)" >];
  proof_lem ppvernac lems;
  if not !Globals.quiet_flag then ppvernac [< strnl "(* END-PROOF *)" >];
;;

(**************************************)
(* Prelude and exit of Coq's toplevel *)
(**************************************)

let opens = [ "Pp"; "Term" ]

let open_libs =
  List.fold_left (fun s e -> [< s; strnl ("open " ^ e ^ ";;") >]) [< >]

let prelude (inc, outc) fnm =
  let strm =
    [< strnl "Drop."; open_libs opens;
       camlp ("let outc = open_out \"" ^ fnm ^ "\"");
       camlp "let ftr = Pp_control.with_output_to outc";
       camlp "let parse_vernac = Pcoq.parse_string Pcoq.Vernac_.vernac";
       strnl "let ppvernac t = (msgnl_with ftr (Ppvernacnew.pr_vernac t); ";
       camlp "flush outc)" >] in
  begin
    flush_strm strm outc;
    read_msg inc
  end

let exit (inc, outc) =
  let strm = [< camlp "flush outc"; camlp "close_out outc";
                camlp "Toplevel.loop ()"; coqp "Quit" >] in
  begin
    flush_strm strm outc;
    read_msg inc
  end

(*************************)
(* Translation using Coq *)
(*************************)

let cmd pgm =
  let cnm = try (Sys.getenv "COQBIN") ^ pgm
            with | Not_found -> pgm in
  if Sys.file_exists cnm then cnm
  else failwith "Error: Coq is not accessible!"

let get_filename = function
  | None -> Filename.temp_file "zenon" "coq.v"
  | Some f -> f

let print_proof fnm = function
  | None ->
    let inc = open_in fnm in
    (try while true do print_endline (input_line inc) done
     with End_of_file -> close_in inc)
  | _ -> ()

let verify valid fnm =
  if valid then
    let pgm = cmd "coqc" in
    let pid = Unix.create_process pgm [|pgm;fnm|]
                                  Unix.stdin Unix.stdout Unix.stderr in
    begin
      print_endline "(* VALIDATION *)";
      match (Unix.waitpid [] pid) with
      | _, Unix.WEXITED 0 ->
        print_endline "The proof has been verified by Coq!"; 0
      | _ -> print_endline "Error: the proof has not been verified by Coq!"; 1
    end
  else 0

let clean fnm = function
  | None ->
      begin try
        Sys.remove fnm;
        Sys.remove (Filename.chop_suffix fnm "v" ^ "vo");
      with Sys_error _ -> ()
      end
  | _ -> ()

let produce_proof_coq ofn valid llp =
  let pgm = cmd "coqtop.byte"
  and fnm = get_filename ofn in
  let coq_ind, coq_outd = Unix.pipe ()
  and zenon_ind, zenon_outd = Unix.pipe () in
  let coq_outc = Unix.out_channel_of_descr coq_outd
  and zenon_inc = Unix.in_channel_of_descr zenon_ind
  and pid = Unix.create_process pgm [|pgm|] coq_ind zenon_outd zenon_outd in
  let chns = zenon_inc, coq_outc in
  let ppvernac = ppvernac_coq chns in
  begin
    Unix.set_nonblock zenon_ind;
    set_binary_mode_in zenon_inc false;
    set_binary_mode_out coq_outc false;
    prelude chns fnm;
    if !Globals.ctx_flag then begin
      require ppvernac;
      tactic ppvernac;
      declare ppvernac llp;
    end;
    proof ppvernac llp;
    exit chns;
    ignore (Unix.waitpid [] pid);
    print_proof fnm ofn;
    let retcode = verify valid fnm in
    clean fnm ofn;
    retcode
  end

(**********************)
(* Direct translation *)
(**********************)

let open_dir valid fnm = function
  | None -> if valid then open_out fnm else stdout
  | Some f -> open_out f

let close_dir valid outc = function
  | None when valid -> close_out outc
  | Some _ -> close_out outc
  | _ -> ()

let produce_proof_dir ofn valid llp =
  let fnm = get_filename ofn in
  let outc = open_dir valid fnm ofn in
  let ppvernac = ppvernac_dir outc in
  begin
    if !Globals.ctx_flag then begin
      require ppvernac;
      tactic ppvernac;
      declare ppvernac llp;
    end;
    proof ppvernac llp;
    close_dir valid outc ofn;
    print_proof fnm ofn;
    let retcode = verify valid fnm in
    clean fnm ofn;
    retcode
  end

(***************)
(* Translation *)
(***************)

let produce_proof phrases check =
  make_mapping phrases;
  if check then produce_proof_coq else produce_proof_dir
