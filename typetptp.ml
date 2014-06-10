
open Type
open Expr

exception Type_error of string
exception Type_found of etype

module M = Map.Make(String)

(* Environment for typing *)
type env = {
    tff : Type.t list M.t;
}

let tff_mem v env = M.mem v env.tff

let tff_find v env =
    try
        begin match M.find v env.tff with
        | [] -> assert false
        | [t] -> t
        | _ -> raise (Type_error (Printf.sprintf "Single-type variable expected ('%s')" v))
        end
    with Not_found ->
        raise (Type_error (Printf.sprintf "Unknown variable : %s" v))

let tff_add_var e t env = match e with
    | Evar(v, _) ->
            if t = Namespace.univ_name then
                raise (Type_error (Format.sprintf "'untyped' variable '%s' detected in tff context" v))
            else
                { (* env with *) tff = M.add v [atomic t] env.tff }
    | _ -> assert false

let tff_add_type name t env =
    if not (Type.tff_check t) then
        raise (Type_error (Printf.sprintf "The following type is ill-formed in TFF :@\n%s" (Type.to_string t)));
    if tff_mem name env then
        match M.find name env.tff with
        | [] -> assert false
        | [t'] -> begin match Type.compare t t' with
            | 0 -> env
            | _ -> raise (Type_error (Printf.sprintf "Contradictory types for '%s'" name))
            end
        | _ -> raise (Type_error (Printf.sprintf "trying to redefine built_in '%s'" name))
    else
        env

let tff_app_aux args t =
    try
        ignore (type_app t args);
        raise (Type_found t)
    with
    | Not_enough_args
    | Function_expected
    | Mismatch _ ->
            ()

let tff_app f args env =
    try
        begin match M.find f env with
        | [] -> assert false
        | l ->
                try
                    List.iter (tff_app_aux args) l;
                    raise (Type_error
                        (Printf.sprintf "No signature match found for '%s' with arguments : %s"
                        f (String.concat "*" (List.map Type.to_string args))
                    ))
                with Type_found t ->
                    t
        end
    with Not_found ->
        raise (Type_error (Printf.sprintf "Unknown variable : %s" f))

let tff_default_env =
    { tff = M.empty }

(* Typing *)
let type_tff_def env e = env
let type_tff_expr env e = e, env
let type_fof_expr e = ()


(* Wrappers *)
let relevant = function
    | Phrase.Hyp(_, _, 13) -> false
    | _ -> true

let is_tff_def s = (s  = 13)
let is_tff_expr s = (10 <= s && s <= 12)
let notype_kind = function
    | s when is_tff_expr s -> s - 10
    | s -> s

let type_phrase env p = match p with
    | Phrase.Hyp (name, e, kind) when is_tff_def kind ->
            p, type_tff_def env e
    | Phrase.Hyp (name, e, kind) when is_tff_expr kind ->
            let e', env' = type_tff_expr env e in
            Phrase.Hyp (name, e', notype_kind kind), env'
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
