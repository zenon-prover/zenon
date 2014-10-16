(* AST corresponding to a Dedukti output *)
type dkvar = string

type dkterm = private
  | Dkvar of dkvar
  | Dklam of dkterm * dkterm * dkterm
  | Dkpi of dkterm * dkterm * dkterm
  | Dkapp of dkterm list
  | Dkarrow of dkterm * dkterm
  | Dkprf
  | Dktermtype
  | Dkproptype
  | Dkanyterm
  | Dknot
  | Dkand
  | Dkor
  | Dkimply
  | Dkforall
  | Dkexists
  | Dktrue
  | Dkfalse
  | Dkeq
  | Dknotc
  | Dkandc
  | Dkorc
  | Dkimplyc
  | Dkforallc
  | Dkexistsc
  | Dktruec
  | Dkfalsec
  | Dkeqc
  | Dkequiv

type dkline = private
  | Dkdecl of dkterm * dkterm
  | Dkdeftype of dkterm * dkterm * dkterm
  | Dkprelude of string
  | Dkrewrite of (dkterm * dkterm) list * dkterm * dkterm

(* constructor functions *)
val dkvar : dkvar -> dkterm
val dklam : dkterm -> dkterm -> dkterm -> dkterm
val dklams : dkterm list -> dkterm list -> dkterm -> dkterm
val dkpi : dkterm -> dkterm -> dkterm -> dkterm
val dkapp : dkterm -> dkterm list -> dkterm
val dkapp2 : dkterm -> dkterm -> dkterm
val dkapp3 : dkterm -> dkterm -> dkterm -> dkterm
val dkarrow : dkterm -> dkterm -> dkterm
val dkprf : dkterm -> dkterm
val dktermtype : dkterm
val dkproptype : dkterm
val dkanyterm : dkterm
val dknot : dkterm -> dkterm
val dkand : dkterm -> dkterm -> dkterm
val dkor : dkterm -> dkterm -> dkterm
val dkimply : dkterm -> dkterm -> dkterm
val dkforall : dkterm -> dkterm -> dkterm
val dkexists : dkterm -> dkterm -> dkterm
val dktrue : dkterm
val dkfalse : dkterm
val dkeq : dkterm -> dkterm -> dkterm
val dknotc : dkterm -> dkterm
val dkandc : dkterm -> dkterm -> dkterm
val dkorc : dkterm -> dkterm -> dkterm
val dkimplyc : dkterm -> dkterm -> dkterm
val dkforallc : dkterm -> dkterm -> dkterm
val dkexistsc : dkterm -> dkterm -> dkterm
val dktruec : dkterm
val dkfalsec : dkterm
val dkeqc : dkterm -> dkterm -> dkterm
val dkequiv : dkterm -> dkterm -> dkterm

val dkdecl : dkterm -> dkterm -> dkline
val dkdeftype : dkterm -> dkterm -> dkterm -> dkline
val dkprelude : string -> dkline
val dkrewrite : (dkterm * dkterm) list -> dkterm -> dkterm -> dkline

(* print functions *)
val p_var : out_channel -> dkvar -> unit
val p_term : out_channel -> dkterm -> unit
val p_term_p : out_channel -> dkterm -> unit
val p_terms : out_channel -> dkterm list -> unit
val p_line : out_channel -> dkline -> unit
