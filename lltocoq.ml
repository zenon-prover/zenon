(*  Copyright 2004 INRIA  *)
Version.add "$Id: lltocoq.ml,v 1.3 2004-06-07 19:56:58 delahaye Exp $";;

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
  | Eall (x, t, e, _) ->
    parth [< str "forall "; str x; if t <> "" then [< str ":"; str t >]
             else [< >]; str ","; constr_of_expr e >]
  | Eex (x, t, e, _) ->
    parth [< str "exists "; str x; if t <> "" then [< str ":"; str t >]
             else [< >]; str ","; constr_of_expr e >]
  | _ -> failwith "Error: unexpected expr to translate!"

(***********************)
(* Require's & Tactics *)
(***********************)

let requires = [ "Classical" ]

let make_require lib = [< str "Require Export "; coqp lib >]

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

let get_concl = function
  | [ l ] -> l.proof.conc
  | _ -> failwith "Error: unexpected LL proof!"

let rec list_types = function
  | [ t ] -> [< str t >]
  | e :: l -> [< str e; str ", "; list_types l >]
  | _ -> assert false

let rec make_parameters = function
  | [] -> [< >]
  | e :: l -> [< str "forall "; str e; str ", "; make_parameters l >]

let rec make_prod = function
  | [ t ] -> [< constr_of_expr t; str " -> False" >]
  | e :: l -> [< constr_of_expr e; str " -> "; make_prod l >]
  | _ -> assert false

let declare_types ppvernac types =
  let lst = list_types types in
  ppvernac [< str "Parameters "; lst; coqp " : Set" >]

let normal f = List.fold_left (fun a e -> if f e a then a else a @ [e]) []

let declare_lem chns lem =
  let concl = lem.proof.conc in
  let types = normal (fun e l -> List.mem e l)
                     (List.flatten (List.map type_list concl)) in
  if types <> [] then declare_types chns types

let declare chns = List.iter (declare_lem chns)

(************************)
(* Coq proof generation *)
(************************)

(****************************************************************************)
(* Warning: we use Coq's type inference for free variables. This means that *)
(*          the translation fails if we are too polymorphic.                *)
(****************************************************************************)

let get_name = function
  | [ l ] -> l.name
  | _ -> failwith "Error: unexpected LL proof!"

let get_prooftree = function
  | [ l ] -> l.proof
  | _ -> failwith "Error: unexpected LL proof!"

let rec make_type sort arity =
  if arity = 0 then if sort then [< str "Prop" >] else [< str "_" >]
  else [< str "_ -> "; make_type sort (arity - 1) >]

let rec make_param = function
  | [] -> [< >]
  | (n, (s, a)) :: l -> [< str "forall "; str n; str " : "; make_type s a;
                           str ", "; make_param l >]

let declare_lemma ppvernac name fvar concl =
  ppvernac [< str "Lemma "; str name; str " : "; make_param fvar;
              make_prod concl; coqend >]

let rec gen_name e = [< str " ZH"; ints (hash e) >]

let proof_init ppvernac nfv conc =
  let lnam = List.fold_left (fun s e -> [< s; gen_name e >]) [< >] conc in
  ppvernac [< str "do "; ints nfv; str " intro; intros"; lnam; coqend >]

let proof_end ppvernac = ppvernac [< coqp "Qed" >]

let inst_var = ref []
let reset_var () = inst_var := []

let get_type = function
  | Eex (_, typ, _, _) | Eall (_, typ, _, _) -> typ
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

let proof_rule ppvernac = function
  | Rconnect (Or, e1, e2) ->
    let hyp0 = gen_name (eor (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2 in
    ppvernac [< str "elim"; hyp0; thenc; str "clear"; hyp0; str ";[ intro";
                hyp1; str " | intro"; hyp2; coqp "]" >]
  | Rconnect (Equiv, e1, e2) ->
    let hyp0 = gen_name (eequiv (e1, e2))
    and hyp1 = gen_name (eimply (e1, e2))
    and hyp2 = gen_name (eimply (e2, e1))
    and hyp3 = gen_name e1
    and hyp4 = gen_name e2
    and hyp5 = gen_name (enot e1)
    and hyp6 = gen_name (enot e2) in
    ppvernac [< str "unfold iff in"; hyp0; thenc; str "elim"; hyp0; thenc;
                str "cintro"; hyp1; thenc; str "cintro"; hyp2; thenc;
                str "clear"; hyp0; thenc; str "assert ("; hyp3; str " : ";
                constr_of_expr e1; str "); [ apply NNPP; red; cintro"; hyp5;
                thenc; str "assert ("; hyp6; str " : ~"; constr_of_expr e2;
                str "); [ red; cintro"; hyp4; thenc; str "generalize ("; hyp2;
                hyp4; str ")"; thenc; str "auto | clear"; hyp1; hyp2;
                str " ] | generalize ("; hyp1; hyp3; str "); cintro"; hyp4;
                thenc; str "clear"; hyp1; hyp2; coqp " ]" >]
  | Rnotconnect(Equiv, e1, e2) ->
    let hyp0 = gen_name (enot (eequiv (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1)
    and hyp4 = gen_name (enot e2) in
    ppvernac [< str "apply"; hyp0; thenc; str "clear"; hyp0; thenc;
                str "split;[ try intro"; hyp1; thenc;
                str "apply NNPP; red; try intro"; hyp4;
                str " | try intro"; hyp2; thenc;
                str "apply NNPP; red; try intro"; hyp3; coqp "]" >]
  | Rnotnot (p as e) ->
    let hyp0 = gen_name (enot (enot e))
    and hyp1 = gen_name p in
    ppvernac [< str "apply"; hyp0; thenc; str "clear"; hyp0; thenc;
                str "intro"; hyp1; coqend >]
  | Rnotex (p, t) ->
    let hyp = gen_name (enot p) in
    begin
      ppvernac [< str "red in "; hyp; thenc; str "apply "; hyp; thenc;
                  str "clear "; hyp; coqend >];
      declare_inst ppvernac (get_type p) t;
      ppvernac [< str "exists "; constr_of_expr t; thenc;
                  str "apply NNPP; red; intro"; inst_name t p; coqend >]
    end
  | Rall (p, t) ->
    let hyp = gen_name p in
    begin
      declare_inst ppvernac (get_type p) t;
      ppvernac [< str "generalize ("; hyp; str " "; constr_of_expr t;
                  str "); intro"; inst_name t p; coqend >]
    end
  | Rlemma (n, args) ->
    ppvernac [< str "intros; eapply "; if args = [] then str n else
                [< List.fold_left (fun s e -> [< s; str " "; str e >])
                [< str "("; str n >] args; str ")" >]; thenc; coqp "eauto" >]
  | _ -> ppvernac [< coqp "auto" >]

let rec proof_build ppvernac pft =
  begin
    proof_rule ppvernac pft.rule;
    List.iter (proof_build ppvernac) pft.hyps;
  end

let proof_script ppvernac n pft =
  begin
    proof_init ppvernac n pft.conc;
    reset_var ();
    proof_build ppvernac pft;
    proof_end ppvernac
  end

let proof_lem ppvernac lem =
  let name = lem.name
  and concl = lem.proof.conc
  and pft = lem.proof in
  let fvar = normal (fun (e, _) l -> List.mem_assoc e l)
                    (List.flatten (List.map free_var concl)) in
  begin
    declare_lemma ppvernac name fvar concl;
    proof_script ppvernac (List.length fvar) pft
  end

let proof ppvernac = List.iter (proof_lem ppvernac)

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
    (try (Sys.remove fnm; Sys.remove ((Filename.chop_suffix fnm "v") ^ "vo"))
     with Sys_error _ -> ())
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
    require ppvernac;
    tactic ppvernac;
    declare ppvernac llp;
    proof ppvernac llp;
    exit chns;
    ignore (Unix.waitpid [] pid);
    print_proof fnm ofn;
    let retcode = verify valid fnm in
    clean fnm ofn; retcode
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
    require ppvernac;
    tactic ppvernac;
    declare ppvernac llp;
    proof ppvernac llp;
    close_dir valid outc ofn;
    print_proof fnm ofn;
    let retcode = verify valid fnm in
    if valid then clean fnm ofn; retcode
  end

(***************)
(* Translation *)
(***************)

let produce_proof check =
  if check then produce_proof_coq else produce_proof_dir
