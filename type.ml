
open Expr
open Format

exception Type_error of string

module M = Map.Make(struct type t = string let compare = Pervasives.compare end)

(* Types for TFF *)
type tff_type =
    | Base of string
    | Arrow of ((string list) * string) list (* support overloading *)

let strip = function Base s -> s | _ -> assert false

let tff_bool = Base "$o"
let tff_int = Base "$int"
let tff_rat = Base "$rat"
let tff_real = Base "$real"

let tff_is_bool = function Base "$o" -> true | _ -> false
let tff_is_num = function Base "$int" | Base "$rat" | Base "$real" -> true | _ -> false
let tff_is_num_r = function Base "$rat" | Base "$real" -> true | _ -> false
let tff_is_atomic = function Base _ -> true | Arrow _ -> false
let tff_is_fun = function Base _ -> false | Arrow _ -> true

let tff_to_string = function
    | Base s -> s
    | Arrow t -> String.concat " or " (List.map (fun (l, s) -> (String.concat ", " l) ^ " -> " ^ s) t)

let set_tff_type t e = add_type (tff_to_string t) e

let get_type = function
    | Etrue | Efalse -> "$o"
    | e -> begin match priv_type e with
        | None -> Namespace.univ_name
        | Some s -> s
    end

let tff_of_expr = function
    | Evar (t, _) -> t
    | _ -> raise (Type_error "Expected a type, not an expression")

let tff_of_lexpr = function
    | [] -> assert false
    | [Evar(t, _)] -> Base t
    | (Evar(t, _)) :: l -> Arrow [List.map tff_of_expr l, t]
    | _ -> raise (Type_error "Expected a type, not an expression")

(* Typing Environnment for TFF *)
type tff_env = {
    types : tff_type M.t;
}

let tff_empty_env = {
    types = M.empty;
}

let tff_find_type v env =
    try
        M.find v env.types
    with Not_found ->
        raise (Type_error ("Unknow variable : " ^ v))

let tff_mem v env = M.mem v env.types

let tff_add_var env v t = match v with
    | Evar (s, _) ->
            if t = Namespace.univ_name then
                raise (Type_error "'untyped' variable detected.")
            else
                { (* env with *) types = M.add s (Base t) env.types; }
    | _ -> assert false

let tff_add_type env name t =
    { (* env with *) types = M.add name t env.types }

exception Type_found of tff_type
let tff_match_app env f args =
    let aux (l, t) = if (List.map (fun x -> Base x) l) = args then raise (Type_found (Base t)) in
    match (tff_find_type f env) with
    | Base _ as t -> t
    | Arrow t ->
            try
                List.iter aux t;
                raise (Type_error ("No signature match found for " ^ f))
            with Type_found t' -> t'


let tff_default_env =
    let int_id = ["$int"],"$int"
    and rat_id = ["$rat"], "$rat"
    and real_id = ["$real"], "$real"
    and int_id_2 = ["$int"; "$int"], "$int"
    and rat_id_2 = ["$rat"; "$rat"], "$rat"
    and real_id_2 = ["$real"; "$real"], "$real"
    and int_pred = ["$int"], "$o"
    and rat_pred = ["$rat"], "$o"
    and real_pred = ["$real"], "$o"
    and int_pred_2 = ["$int"; "$int"], "$o"
    and rat_pred_2 = ["$rat"; "$rat"], "$o"
    and real_pred_2 = ["$real"; "$real"], "$o"
    in
    let base = [
        "$less",        Arrow [int_pred_2; rat_pred_2; real_pred_2];
        "$lesseq",      Arrow [int_pred_2; rat_pred_2; real_pred_2];
        "$greater",     Arrow [int_pred_2; rat_pred_2; real_pred_2];
        "$greatereq",   Arrow [int_pred_2; rat_pred_2; real_pred_2];
        "$uminus",      Arrow [int_id; rat_id; real_id];
        "$sum",         Arrow [int_id_2; rat_id_2; real_id_2];
        "$difference",  Arrow [int_id_2; rat_id_2; real_id_2];
        "$product",     Arrow [int_id_2; rat_id_2; real_id_2];
        "quotient",     Arrow [rat_id_2; real_id_2];
        "quotient_e",   Arrow [int_id_2; rat_id_2; real_id_2];
        "quotient_t",   Arrow [int_id_2; rat_id_2; real_id_2];
        "quotient_f",   Arrow [int_id_2; rat_id_2; real_id_2];
        "remainder_e",  Arrow [int_id_2; rat_id_2; real_id_2];
        "remainder_t",  Arrow [int_id_2; rat_id_2; real_id_2];
        "remainder_f",  Arrow [int_id_2; rat_id_2; real_id_2];
        "$floor",       Arrow [int_id; rat_id; real_id];
        "$ceiling",     Arrow [int_id; rat_id; real_id];
        "$truncate",    Arrow [int_id; rat_id; real_id];
        "$round",       Arrow [int_id; rat_id; real_id];
        "$is_int",      Arrow [int_pred; rat_pred; real_pred];
        "$is_rat",      Arrow [int_pred; rat_pred; real_pred];
        "$to_int",      Arrow [["$int"], "$int"; ["$rat"], "$int"; ["$real"], "$int"];
        "$to_rat",      Arrow [["$int"], "$rat"; ["$rat"], "$rat"; ["$real"], "$rat"];
        "$to_real",     Arrow [["$int"], "$real"; ["$rat"], "$real"; ["$real"], "$real"];
    ] in
    let env = tff_empty_env in
    let def = List.fold_left (fun acc (s, t) -> M.add s t acc) env.types base in
    { types = def; }

(* DEBUG CODE *)
let rec print_expr fmt f = match f with
    | Evar (s, _) ->        fprintf fmt "@[<hov 4>Var (%s):@ %s@]" (get_type f) s
    | Emeta (e, _) ->       fprintf fmt "@[<hov 4>Meta (%s):@ %a@]" (get_type f) print_expr e
    | Eapp (s, l, _) ->     fprintf fmt "@[<hov 4>App (%s) %s :@ %a@]" (get_type f) s print_list_expr l
    | Enot (e, _) ->        fprintf fmt "@[<hov 4>Not :@\n%a@]" print_expr e
    | Eand (e, e', _) ->    fprintf fmt "  @[<hov>%a@]@\nAND@\n  @[<hov>%a@]" print_expr e print_expr e'
    | Eor (e, e', _) ->     fprintf fmt "  @[<hov>%a@]@\nOR@\n  @[<hov>%a@]" print_expr e print_expr e'
    | Eimply (e, e', _) ->  fprintf fmt "  @[<hov>%a@]@\nIMPLY@\n  @[<hov>%a@]" print_expr e print_expr e'
    | Eequiv (e, e', _) ->  fprintf fmt "  @[<hov>%a@]@\nEQUIV@\n  @[<hov>%a@]" print_expr e print_expr e'
    | Etrue ->              fprintf fmt "TRUE"
    | Efalse ->             fprintf fmt "FALSE"
    | Eall (e, t, e', _) -> fprintf fmt "@[<hov 4>ALL (%s : %a):@\n%a@]" t print_expr e print_expr e'
    | Eex (e, t, e', _) ->  fprintf fmt "@[<hov 4>EX (%s : %a):@\n%a@]" t print_expr e print_expr e'
    | Etau (e, t, e', _) -> fprintf fmt "@[<hov 4>TAU (%s : %a):@\n%a@]" t print_expr e print_expr e'
    | Elam (e, t, e', _) -> fprintf fmt "@[<hov 4>LAM (%s : %a):@\n%a@]" t print_expr e print_expr e'

and print_list_expr fmt l = List.iter (fun e -> fprintf fmt "@[<hov 3>-> %a@]@\n" print_expr e) l
(* END DEBUG CODE *)

let first_chars s n = String.sub s 0 n
let after_chars s n = String.sub s n (String.length s - n)

let is_ttdef s = s = 13
let is_texpr s = (10 <= s && s <= 12)
let notype_kind = function
    | s when is_texpr s -> s - 10
    | s -> s

let var_of_meta = function
    | Emeta (Eall (Evar(v, _), _, _, _), _)
    | Emeta (Eex (Evar(v, _), _, _, _), _) -> v
    | _ -> assert false

let type_of_meta = function
    | Emeta (Eall (Evar(_, _), t, _, _), _)
    | Emeta (Eex (Evar(_, _), t, _, _), _) -> Base t
    | _ -> assert false

let rec type_tff_aux env e =
    let rec aux e = match e with
    | Evar (v, _) -> (tff_find_type v env), e
    | Emeta (e', _) ->
            assert false (*
            let v = var_of_meta e in
            if tff_mem v env && ((tff_find_type v env) <> (type_of_meta e)) then
                raise (Type_error "Type conflict.")
            else
                (type_of_meta e), e *)
    | Eapp (s, l, _) ->
            type_tff_app env s l
    | Enot (e', _) ->
            let t', e' = type_tff_aux env e' in
            if tff_is_bool t' then
                tff_bool, (enot e')
            else
                raise (Type_error "Negation of a non-boolean.")
    | Eand (e', e'', _) ->
            let t', e' = type_tff_aux env e' in
            let t'', e'' = type_tff_aux env e'' in
            if tff_is_bool t' && tff_is_bool t'' then
                tff_bool, eand (e', e'')
            else
                raise (Type_error "Boolean combination of non-boolean elements (and).")
    | Eor (e', e'', _) ->
            let t', e' = type_tff_aux env e' in
            let t'', e'' = type_tff_aux env e'' in
            if tff_is_bool t' && tff_is_bool t'' then
                tff_bool, eor (e', e'')
            else
                raise (Type_error "Boolean combination of non-boolean elements (or).")
    | Eimply (e', e'', _) ->
            let t', e' = type_tff_aux env e' in
            let t'', e'' = type_tff_aux env e'' in
            if tff_is_bool t' && tff_is_bool t'' then
                tff_bool, eimply (e', e'')
            else
                raise (Type_error "Boolean combination of non-boolean elements (imply).")
    | Eequiv (e', e'', _) ->
            let t', e' = type_tff_aux env e' in
            let t'', e'' = type_tff_aux env e'' in
            if tff_is_bool t' && tff_is_bool t'' then
                tff_bool, eequiv (e', e'')
            else
                raise (Type_error "Boolean combination of non-boolean elements (equiv).")
    | Etrue
    | Efalse ->
            tff_bool, e
    | Eall (Evar (s, _) as v, t, body, _) ->
            let t', body = type_tff_aux (tff_add_var env v t) body in
            if tff_is_bool t' then
                tff_bool, eall (v, t, body)
            else
                raise (Type_error "Quantification over non-boolean expression (forall).")
    | Eex (Evar (s, _) as v, t, body, _) ->
            let t', body = type_tff_aux (tff_add_var env v t) body in
            if tff_is_bool t' then
                tff_bool, eex (v, t, body)
            else
                raise (Type_error "Quantification over non-boolean expression (exists).")
    | Etau (Evar (s, _), t, body, _) ->
            assert false
    | Elam (Evar (s, _), t, body, _) ->
            assert false
    | _ -> raise (Type_error "Ill-formed expression.")
    in
    let t, e = aux e in
    t, set_tff_type t e

and type_tff_app env s l = match s, l with
    | "=", [a; b]  ->
            let t, e = type_tff_aux env a in
            let t', e' = type_tff_aux env b in
            if tff_is_atomic t && tff_is_atomic t' && t = t' then
                if tff_is_num t then
                    tff_bool, eapp ("$eq_num", [e; e'])
                else
                    tff_bool, eapp (s, [e; e'])
            else
                raise (Type_error ("Bad types for equality : " ^ (tff_to_string t) ^ " <> " ^ (tff_to_string t')))
    | "$int", [Evar (v, _)] ->
            tff_int, eapp (v, [])
    | "$rat", [Evar (v, _)] ->
            tff_rat, eapp (v, [])
    | "$real", [Evar (v, _)] ->
            tff_real, eapp (v, [])
    | _ ->
            let l', l'' = List.split (List.map (type_tff_aux env) l) in
            let t = tff_match_app env s l' in
            t, eapp (s, l'')

let type_tff_expr env e =
    let t, e' = type_tff_aux env e in
    match t with
    | Base "$o" -> e'
    | _ -> raise (Type_error ("Expected a boolean, not a " ^ (tff_to_string t)))

let type_tff_def env = function
    | Eapp ("#", Evar(s, _) :: l, _) -> tff_add_type env s (tff_of_lexpr l)
    | _ -> raise (Type_error "Not a definition")

let rec type_fof_expr e = match e with
    | Evar _
    | Etrue
    | Efalse ->
            ()
    | Emeta (v, _) ->
            type_fof_expr v
    | Eapp (_, l, _) ->
            List.iter type_fof_expr l
    | Enot (e', _) ->
            type_fof_expr e'
    | Eand (e', e'', _)
    | Eor (e', e'', _)
    | Eimply (e', e'', _)
    | Eequiv (e', e'', _) ->
            type_fof_expr e';
            type_fof_expr e''
    | Eall (e', t, e'', _)
    | Eex (e', t, e'', _)
    | Etau (e', t, e'', _)
    | Elam (e', t, e'', _) ->
            if t <> Namespace.univ_name then
                raise (Type_error "Typed variable in untyped formula.");
            type_fof_expr e';
            type_fof_expr e''

let relevant = function
    | Phrase.Hyp(_, _, 13) -> false
    | _ -> true

let type_phrase env p = match p with
    | Phrase.Hyp (name, e, kind) when is_ttdef kind ->
            p, type_tff_def env e
    | Phrase.Hyp (name, e, kind) when is_texpr kind ->
            let e' = type_tff_expr env e in
            (* eprintf "%a@." print_expr e'; *)
            Phrase.Hyp (name, e', notype_kind kind), env
    | Phrase.Hyp (name, e, kind) ->
            type_fof_expr e;
            p, env
    | _ -> p, env

let map_fold f s l =
    let e, env = List.fold_left (fun (acc, env) e -> let x, env' = f env e in (x :: acc, env')) ([], s) l in
    List.rev e, env

let typecheck l =
    let p, _ = map_fold type_phrase tff_default_env l in
    List.filter relevant p
