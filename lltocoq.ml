(*  Copyright 2004 INRIA  *)
Version.add "$Id: lltocoq.ml,v 1.1 2004-05-24 13:47:55 delahaye Exp $";;

(********************************************************************)
(* Some preliminary remarks:                                        *)
(*   - we use Coq V8 and higher (V7 is not supported)               *)
(*   - we use Coq's pretty-printer (using the bytecode version)     *)
(*   - we use "Unixies" but all of them are supported under Windows *)
(********************************************************************)

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

(**************************************)
(* Pretty-print functions (using Coq) *)
(**************************************)

let ppvernac outc s =
  flush_strm [< str "ppvernac (parse_vernac \""; s; camlp "\")" >] outc

let pptac outc indent s =
  let spc = String.make indent ' ' in
  flush_strm [< str spc; str "ppvernac (parse_vernac \""; s; camlp "\")" >]
    outc

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

(*************)
(* Require's *)
(*************)

let requires = [ "Classical" ]

let make_require lib = [< str "Require Export "; coqp lib >]

let require outc =
  let req = List.fold_left (fun s e -> [< s; make_require e >])
                           [< >] requires in
  ppvernac outc req

(**********************)
(* Type  declarations *)
(**********************)

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

let declare_types outc types =
  let lst = list_types types in
  ppvernac outc [< str "Parameters "; lst; coqp " : Set" >]

let normal = List.fold_left (fun a e -> if List.mem e a then a else a @ [e]) []

let declare_lem outc lem =
  let concl = lem.proof.conc in
  let types = normal (List.flatten (List.map type_list concl)) in
  if types <> [] then declare_types outc types

let declare outc = List.iter (declare_lem outc)

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

let rec make_param = function
  | [] -> [< >]
  | e :: l -> [< str "forall "; str e; str ", "; make_param l >]

let declare_lemma outc name fvar concl =
  ppvernac outc [< str "Lemma "; str name; str " : "; make_param fvar;
                   make_prod concl; coqend >]

let rec gen_name e = [< str " ZH"; ints (hash e) >]

let proof_init outc nfv conc =
  let lnam = List.fold_left (fun s e -> [< s; gen_name e >]) [< >] conc in
  ppvernac outc [< str "do "; ints nfv; str "intro; intros"; lnam; coqend >]

let proof_end outc = ppvernac outc [< coqp "Qed" >]

let inst_var = ref []
let reset_var () = inst_var := []

let get_type = function
  | Eex (_, typ, _, _) | Eall (_, typ, _, _) -> typ
  | _ -> assert false

let declare_inst outc typ = function
  | Evar (x, _) when String.length x > 2 && (String.sub x 0 2) = "_Z" &&
                     not(List.mem x !inst_var) ->
    begin
      inst_var := x :: !inst_var;
      ppvernac outc [< str "Parameter "; str x; str " : "; coqp typ >]
    end
  | _ -> ()

let inst_name t = function
  | Eex (x, _, e, _) -> let ti = enot (substitute [ x, t ] e) in gen_name ti
  | Eall (x, _, e, _) -> let ti = substitute [ x, t ] e in gen_name ti
  | _ -> assert false

let proof_rule outc = function
  | Rconnect (Or, e1, e2) ->
    let hyp0 = gen_name (eor (e1, e2))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2 in
    ppvernac outc [< str "elim"; hyp0; thenc; str "clear"; hyp0;
                     str ";[ intro"; hyp1; str " | intro"; hyp2; coqp "]" >]
  | Rnotconnect(Equiv, e1, e2) ->
    let hyp0 = gen_name (enot (eequiv (e1, e2)))
    and hyp1 = gen_name e1
    and hyp2 = gen_name e2
    and hyp3 = gen_name (enot e1)
    and hyp4 = gen_name (enot e2) in
    ppvernac outc [< str "apply"; hyp0; thenc; str "clear"; hyp0; thenc;
                     str "split;[ try intro"; hyp1; thenc;
                     str "apply NNPP; red; try intro"; hyp4;
                     str " | try intro"; hyp2; thenc;
                     str "apply NNPP; red; try intro"; hyp3; coqp "]" >]
  | Rnotnot (p as e) ->
    let hyp0 = gen_name (enot (enot e))
    and hyp1 = gen_name p in
    ppvernac outc [< str "apply"; hyp0; thenc; str "clear"; hyp0; thenc;
                     str "intro"; hyp1; coqend >]
  | Rnotex (p, t) ->
    let hyp = gen_name (enot p) in
    begin
      ppvernac outc [< str "red in "; hyp; thenc; str "apply "; hyp; thenc;
                       str "clear "; hyp; coqend >];
      declare_inst outc (get_type p) t;
      ppvernac outc [< str "exists "; constr_of_expr t; thenc;
                       str "apply NNPP; red; intro"; inst_name t p; coqend >]
    end
  | Rall (p, t) ->
    let hyp = gen_name p in
    begin
      declare_inst outc (get_type p) t;
      ppvernac outc [< str "generalize ("; hyp; str " "; constr_of_expr t;
                       str "); intro"; inst_name t p; coqend >]
    end
  | _ -> ppvernac outc [< coqp "auto" >]

let rec proof_build outc pft =
  begin
    proof_rule outc pft.rule;
    List.iter (proof_build outc) pft.hyps
  end

let proof_script outc n pft =
  begin
    proof_init outc n pft.conc;
    reset_var ();
    proof_build outc pft;
    proof_end outc
  end

let proof_lem outc lem =
  let name = lem.name
  and concl = lem.proof.conc
  and pft = lem.proof in
  let fvar = normal (List.flatten (List.map free_var concl)) in
  begin
    declare_lemma outc name fvar concl;
    proof_script outc (List.length fvar) pft
  end

let proof outc = List.iter (proof_lem outc)

(**************************************)
(* Prelude and exit of Coq's toplevel *)
(**************************************)

let opens = [ "Pp"; "Term" ]

let open_libs =
  List.fold_left (fun s e -> [< s; strnl ("open " ^ e ^ ";;") >]) [< >]

let prelude outc fnm =
  let strm =
    [< strnl "Drop."; open_libs opens;
       camlp ("let outc = open_out \"" ^ fnm ^ "\"");
       camlp "let ftr = Pp_control.with_output_to outc";
       camlp "let parse_vernac = Pcoq.parse_string Pcoq.Vernac_.vernac";
       camlp "let ppvernac t = msgnl_with ftr (Ppvernacnew.pr_vernac t)" >] in
  flush_strm strm outc

let exit outc =
  let strm =
    [< camlp "flush outc";
 camlp "close_out outc"; strnl "Toplevel.loop ();;"; strnl "Quit." >] in
  flush_strm strm outc

(***************)
(* Coq process *)
(***************)

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
  | None -> Sys.remove fnm
  | _ -> ()

let produce_proof ofn valid llp =
  let pgm = cmd "coqtop.byte"
  and fnm = get_filename ofn in
  let coq_ind, coq_outd = Unix.pipe ()
  and zenon_ind, zenon_outd = Unix.pipe () in
  let coq_outc = Unix.out_channel_of_descr coq_outd
  and zenon_inc = Unix.in_channel_of_descr zenon_ind
  and pid = Unix.create_process pgm [|pgm|] coq_ind zenon_outd zenon_outd in
  begin
    set_binary_mode_in zenon_inc false;
    set_binary_mode_out coq_outc false;
    prelude coq_outc fnm;
    require coq_outc;
    declare coq_outc llp;
    proof coq_outc llp;
    exit coq_outc;
    ignore (Unix.waitpid [] pid);
    print_proof fnm ofn;
    let retcode = verify valid fnm in
    clean fnm ofn; retcode
  end
