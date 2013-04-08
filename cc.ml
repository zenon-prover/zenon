(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 Functional Congruence Closure} *)


(** {2 Curryfied terms} *)

module type CurryfiedTerm = sig
  type symbol
  type t = private {
    shape : shape;      (** Which kind of term is it? *)
    tag : int;          (** Unique ID *)
  } (** A curryfied term *)
  and shape = private
    | Const of symbol   (** Constant *)
    | Apply of t * t    (** Curryfied application *)

  val mk_const : symbol -> t
  val mk_app : t -> t -> t
  val get_id : t -> int
end

module Curryfy(X : Hashtbl.HashedType) = struct
  type symbol = X.t
  type t = {
    shape : shape;      (** Which kind of term is it? *)
    tag : int;          (** Unique ID *)
  }
  and shape =
    | Const of symbol   (** Constant *)
    | Apply of t * t    (** Curryfied application *)

  type term = t

  module WE = Weak.Make(struct
    type t = term
    let equal a b = match a.shape, b.shape with
      | Const ia, Const ib -> X.equal ia ib
      | Apply (a1,a2), Apply (b1,b2) -> a1 == a2 && b1 == b2
      | _ -> false
    let hash a = match a.shape with
      | Const i -> X.hash i
      | Apply (a, b) -> a.tag * 65539 + b.tag
  end)

  let __table = WE.create 10001
  let count = ref 0

  let hashcons t =
    let t' = WE.merge __table t in
    (if t == t' then incr count);
    t'

  let mk_const i =
    let t = {shape=Const i; tag= !count; } in
    hashcons t

  let mk_app a b =
    let t = {shape=Apply (a, b); tag= !count; } in
    hashcons t

  let get_id t = t.tag
end

(** {2 Congruence Closure} *)

module type S = sig
  module CT : CurryfiedTerm

  type t
    (** Congruence Closure instance *)

  exception Inconsistent of CT.t * CT.t
    (** Exception raised when equality and inequality constraints are
        inconsistent. The two given terms should be different
        but are equal. *)

  val create : int -> t
    (** Create an empty CC of given size *)

  val add : t -> CT.t -> t
    (** Add the given term to the CC *)

  val assert_eq : t -> CT.t -> CT.t -> t
    (** Assert that the two terms are equal (may raise Inconsistent) *)

  val assert_diff : t -> CT.t -> CT.t -> t
    (** Assert that the two given terms are distinct (may raise Inconsistent) *)

  type action =
    | AssertEq of CT.t * CT.t
    | AssertDiff of CT.t * CT.t
    (** Action that can be performed on the CC *)

  val assert_action : t -> action -> t

  val eq : t -> CT.t -> CT.t -> bool
    (** Check whether the two terms are equal *)

  val can_eq : t -> CT.t -> CT.t -> bool
    (** Check whether the two terms can be equal *)

  val iter_equiv_class : t -> CT.t -> (CT.t -> unit) -> unit
    (** Iterate on terms that are congruent to the given term *)

  val explain : t -> CT.t -> CT.t -> action list
    (** Explain why those two terms are equal (they must be) *)
end

module Make(T : CurryfiedTerm) = struct
  module CT = T
  module Puf = Puf.Make(CT)

  (* Persistent Hashtable on curryfied terms *)
  module THashtbl = PersistentHashtbl.Make(struct
    type t = CT.t
    let equal t1 t2 = t1.CT.tag = t2.CT.tag
    let hash t = t.CT.tag
  end)

  (* Persistent Hashtable on pairs of curryfied terms *)
  module T2Hashtbl = PersistentHashtbl.Make(struct
    type t = CT.t * CT.t
    let equal (t1,t1') (t2,t2') = t1.CT.tag = t2.CT.tag && t1'.CT.tag = t2'.CT.tag
    let hash (t,t') = t.CT.tag * 65539 + t'.CT.tag
  end)

  type t = {
    uf : Puf.t;
    use : CT.t list THashtbl.t;   (* for all repr a, a -> all f(a,b) and f(c,a) *)
    lookup : eqn T2Hashtbl.t;     (* for all reprs a,b, some f(a,b)=c (if any) *)
  } (** Congruence Closure data structure *)
  and eqn = CT.t * CT.t
    (** Equation between two terms *)

  exception Inconsistent of CT.t * CT.t
    (** Exception raised when equality and inequality constraints are
        inconsistent. The two given terms should be different
        but are equal. *)

  (*
  val create : int -> t
    (** Create an empty CC of given size *)

  val add : t -> CT.t -> t
    (** Add the given term to the CC *)

  val assert_eq : t -> CT.t -> CT.t -> t
    (** Assert that the two terms are equal (may raise Inconsistent) *)

  val assert_diff : t -> CT.t -> CT.t -> t
    (** Assert that the two given terms are distinct (may raise Inconsistent) *)

  type action =
    | AssertEq of CT.t * CT.t
    | AssertDiff of CT.t * CT.t
    (** Action that can be performed on the CC *)

  val assert_action : t -> action -> t

  val eq : t -> CT.t -> CT.t -> bool
    (** Check whether the two terms are equal *)

  val can_eq : t -> CT.t -> CT.t -> bool
    (** Check whether the two terms can be equal *)

  val iter_equiv_class : t -> CT.t -> (CT.t -> unit) -> unit
    (** Iterate on terms that are congruent to the given term *)

  val explain : t -> CT.t -> CT.t -> action list
    (** Explain why those two terms are equal (they must be) *)

    *)
end
