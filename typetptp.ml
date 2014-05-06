
open Expr
open Format

exception Type_error of string

module M = Map.Make(struct type t = string let compare = Pervasives.compare end)

(* Types for TFF *)
type tff_type =
    | Base of string
    | Arrow of (string list) * string

let tff_bool = Base "$o"
let tff_int = Base "$int"
let tff_is_bool = function Base "$o" -> true | _ -> false
let tff_is_num = function Base "$int" | Base "$rat" | Base "$real" -> true | _ -> false
let tff_is_num_r = function Base "$rat" | Base "$real" -> true | _ -> false
let tff_is_atomic = function Base _ -> true | Arrow _ -> false
let tff_is_fun = function Base _ -> false | Arrow _ -> true
let tff_type_args = function Base _ -> assert false | Arrow (l, _) -> List.map (fun s -> Base s) l
let tff_type_return = function Base _ -> assert false | Arrow (_, t) -> Base t
let tff_to_string = function
    | Base s -> s
    | Arrow (l, s) -> (String.concat ", " l) ^ " -> " ^ s

let num_type s =
    let is_digit c = match c with
        | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' -> true
        | _ -> false
    in
    (* Manual automata for numbers *)
    let rec aux1 s n = (* starting point *)
        if 0 <= n && n < String.length s then
            if s.[n] = '+' || s.[n] = '-' then aux2 s (n + 1) else aux2 s n
        else
            raise (Type_error "number expected")
    and aux2 s n = (* check for any number *)
        if 0 <= n && n < String.length s then
            if is_digit s.[n] then aux2 s (n + 1) else
            if s.[n] = '/' then let _ = aux3 s (n + 1) in Base "$rat" else
            if s.[n] = '.' then let _ = aux4 s (n + 1) in Base "$real" else
                raise (Type_error "not a number")
        else
            Base "$int"
    and aux3 s n = (* check for a pure integer *)
        if 0 <= n && n < String.length s then
            if is_digit s.[n] then aux3 s (n + 1) else
                raise (Type_error "not an integer")
        else
            Base "$int" (* should not ever be really used *)
    and aux4 s n = (* check for an integer plus an exponent *)
        if 0 <= n && n < String.length s then
            if is_digit s.[n] then aux4 s (n + 1) else
            if s.[n] = 'e' || s.[n] = 'E' then aux5 s (n + 1) else
                raise (Type_error "not a correct real")
        else
            Base "$int" (* should not ever really be used *)
    and aux5 s n = (* check for a pure signed integer *)
        if 0 <= n && n < String.length s then
            if s.[n] = '+' || s.[n] = '-' then aux3 s (n + 1) else aux3 s n
        else
            raise (Type_error "number expected")
    in
    aux1 s 0


(* Typing Environnment for TFF *)
type tff_env = {
    types : tff_type M.t;
}

let empty_tff_env = {
    types = M.empty;
}

let find_tff_type v env =
    try
        M.find v env.types
    with Not_found ->
        raise (Type_error ("Unknow variable : " ^ v))

let tff_mem v env = M.mem v env.types

let tff_add_var env v t = match v with
    | Evar (s, _) ->
            { (* env with *) types = M.add s (Base t) env.types; }
    | _ -> assert false

let tff_default_env =
    let base = [] in
    let env = empty_tff_env in
    let def = List.fold_left (fun acc (s, t) -> M.add s t acc) env.types base in
    { types = def; }

(* DEBUG CODE *)
let rec print_expr fmt = function
    | Evar (s, _) ->        fprintf fmt "@[<hov 4>Var :@\n%s@]" s
    | Emeta (e, _) ->       fprintf fmt "@[<hov 4>Meta :@\n%a@]" print_expr e
    | Eapp (s, l, _) ->     fprintf fmt "@[<hov 4>App (%s) :@\n%a@]" s print_list_expr l
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

let is_typed s = (first_chars s 6) = "typed_"
let notype_kind s = after_chars s 6

let var_of_meta = function
    | Emeta (Eall (Evar(v, _), _, _, _), _)
    | Emeta (Eex (Evar(v, _), _, _, _), _) -> v
    | _ -> assert false

let type_of_meta = function
    | Emeta (Eall (Evar(_, _), t, _, _), _)
    | Emeta (Eex (Evar(_, _), t, _, _), _) -> Base t
    | _ -> assert false

let rec type_tff_aux env e = match e with
    | Evar (v, _) -> (find_tff_type v env), e
    | Emeta (e', _) ->
            (* Typecheck meta-variable body ? *)
            let v = var_of_meta e in
            if tff_mem v env && ((find_tff_type v env) <> (type_of_meta e)) then
                raise (Type_error "Type conflict.")
            else
                (type_of_meta e), e
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
    | Etau (Evar (s, _) as v, t, body, _) ->
            let t', body = type_tff_aux (tff_add_var env v t) body in
            if tff_is_bool t' then
                tff_bool, etau (v, t, body)
            else
                raise (Type_error "Quantification over non-boolean expression (tau).")
    | Elam (Evar (s, _) as v, t, body, _) ->
            let t', body = type_tff_aux (tff_add_var env v t) body in
            if tff_is_bool t' then
                tff_bool, elam (v, t, body)
            else
                raise (Type_error "Quantification over non-boolean expression (lam).")
    | _ -> raise (Type_error "Ill-formed expression.")

and type_tff_app env s l = match s, l with
    | "=", a :: b :: [] ->
            let t, e = type_tff_aux env a in
            let t', e' = type_tff_aux env b in
            if tff_is_atomic t && tff_is_atomic t' && t = t' then
                if tff_is_num t then begin
                    eprintf "transformed an equality@.";
                    tff_bool, eapp ("$eq_num", [e; e'])
                end else
                    tff_bool, eapp (s, [e; e'])
            else
                raise (Type_error ("Bad types for equality : " ^ (tff_to_string t) ^ " <> " ^ (tff_to_string t')))
    | ("$is_int" | "$is_rat"), a :: []  ->
            let t, e = type_tff_aux env a in
            if tff_is_num t then
                tff_bool, eapp (s, [e])
            else
                raise (Type_error ("Wrong type for prediacte " ^ s))
    | ("$less" | "$lesseq" | "$greater" | "$greatereq"), a :: b :: []  ->
            let t, e = type_tff_aux env a in
            let t', e' = type_tff_aux env b in
            if tff_is_num t && tff_is_num t' && t = t' then
                tff_bool, eapp (s, [e; e'])
            else
                raise (Type_error ("Wrong type for prediacte " ^ s))
    | ("$sum" | "$difference" | "$product"), a :: b :: [] ->
            let t, e = type_tff_aux env a in
            let t', e' = type_tff_aux env b in
            if tff_is_num t && tff_is_num t' && t = t' then
                t, eapp (s, [e; e'])
            else
                raise (Type_error ("Wrong type for prediacte " ^ s))
    | "$quotient", a :: b :: [] ->
            let t, e = type_tff_aux env a in
            let t', e' = type_tff_aux env b in
            if tff_is_num_r t && tff_is_num_r t' && t = t' then
                t, eapp (s, [e; e'])
            else
                raise (Type_error ("Wrong type for prediacte " ^ s))
    | s , [] -> num_type s, eapp (s, [])
    | _ -> raise (Type_error ("Unknown operator/ Bad arity for operator " ^ s))

let type_tff_expr env e =
    let t, e' = type_tff_aux env e in
    match t with
    | Base "$o" -> e'
    | _ -> raise (Type_error ("Expected a boolean, not a " ^ (tff_to_string t)))

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

let type_phrase env p = match p with
    | Phrase.Formula (name, kind, e) ->
            if is_typed kind then begin
                (* TODO: in case of a definition, extend environment *)
                let e' = type_tff_expr env e in
                eprintf "%a@." print_expr e';
                Phrase.Formula (name, notype_kind kind, e'), env
            end else begin
                type_fof_expr e;
                p, env
            end
    | _ -> p, env

let map_fold f s l =
    let e, env = List.fold_left (fun (acc, env) e -> let x, env' = f env e in (x :: acc, env')) ([], s) l in
    List.rev e, env

let typecheck x =
    let p, _ = map_fold type_phrase empty_tff_env x in
    p

