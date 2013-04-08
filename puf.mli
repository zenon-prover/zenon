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

(** {1 Functional (persistent) extensible union-find} *)

(** {2 Persistent array} *)

module PArray : sig
  type 'a t

  val make : int -> 'a -> 'a t

  val init : int -> (int -> 'a) -> 'a t

  val get : 'a t -> int -> 'a

  val set : 'a t -> int -> 'a -> 'a t

  val length : 'a t -> int

  val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b

  val extend : 'a t -> int -> 'a -> unit
    (** Extend [t] to the given [size], initializing new elements with [elt] *)

  val extend_init : 'a t -> int -> (int -> 'a) -> unit
    (** Extend [t] to the given [size], initializing elements with [f] *)
end

(** {2 Type with unique identifier} *)

module type ID = sig
  type t
  val get_id : t -> int
end

(** {2 Persistent Union-Find} *)

module type S = sig
  type elt
    (** Elements of the Union-find *)

  type t
    (** An instance of the union-find, ie a set of equivalence classes *)

  val create : int -> t
    (** Create a union-find of the given size. *)

  val find : t -> elt -> elt
    (** [find uf a] returns the current representative of [a] in the given
        union-find structure [uf]. By default, [find uf a = a]. *)

  val union : t -> elt -> elt -> t
    (** [union uf a b] returns an update of [uf] where [find a = find b].
        May raise Inconsistent. *)

  val distinct : t -> elt -> elt -> t
    (** Ensure that the two elements are distinct. May raise Inconsistent *)

  val must_be_distinct : t -> elt -> elt -> bool
    (** Should the two elements be distinct? *)

  val iter_equiv_class : t -> elt -> (elt -> unit) -> unit
    (** [iter_equiv_class uf a f] calls [f] on every element of [uf] that
        is congruent to [a], including [a] itself. *)

  val inconsistent : t -> (elt * elt) option
    (** Check whether the UF is inconsistent *)
end

module Make(X : ID) : S with type elt = X.t
