
open Expr
open Node
open Mlproof
(* module S = Simplex.Make(struct type t = Expr.t let compare = Expr.compare end) *)

(* Helper around the simplex module *)
type simplex = {
    (* core : S.t; *)
    bindings : (expr * expr) list;
}

(* Internal state *)
type state = {
    stack : (expr * simplex) Stack.t;
    todo : (expr * Node.node_item) list; (* could be a map ? *)
}

(* Extension functions *)
let add_formula, remove_formula, to_do =
    let f _ = () in
    f, f, f

(* TODO: rewrite these *)
let lesseq a b = eapp ("$lesseq", [a; b])
let greatereq a b = eapp ("$greatereq", [a; b])
let minus_one e = eapp ("$difference", [e; eapp ("$int", [evar "1"])])
let plus_one e = eapp ("$sum", [e; eapp ("$int", [evar "1"])])

let newnodes e g _ = match e with
    | Enot (Eapp ("$eq_$int", [a; b], _), _) -> [Node {
        nconc = [e];
        nrule = Ext ("arith", "neq", [a; b]);
        nprio = Prop;
        ngoal = g;
        nbranches = [| [lesseq a (minus_one b)]; [greatereq a (plus_one b)] |]; }]
    | _ -> []

let make_inst term g = assert false

let to_llproof f p t = t.(0)

let declare_context_coq fmt = ()

let p_rule_coq fmt r = ()

let predef () = []
;;

Extension.register {
  Extension.name = "arith";
  Extension.newnodes = newnodes;
  Extension.make_inst = make_inst;
  Extension.add_formula = add_formula;
  Extension.remove_formula = remove_formula;
  Extension.preprocess = (fun x -> x);
  Extension.add_phrase = (fun _ -> ());
  Extension.postprocess = (fun x -> x);
  Extension.to_llproof = to_llproof;
  Extension.declare_context_coq = declare_context_coq;
  Extension.p_rule_coq = p_rule_coq;
  Extension.predef = predef;
};;

