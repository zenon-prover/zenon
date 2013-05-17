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

module CurryfiedTerm : sig
  type t
    (** A curryfied term *)

  val mk_const : int -> t
  val mk_app : t -> t -> t
end

(** {2 Congruence Closure} *)

module CC : sig
  type t
    (** Congruence Closure instance *)

  exception Inconsistent of CurryfiedTerm.t * CurryfiedTerm.t
    (** Exception raised when equality and inequality constraints are
        inconsistent. The two given terms should be different
        but are equal. *)

  val create : int -> t
    (** Create an empty CC of given size *)

  val add : t -> CurryfiedTerm.t -> t
    (** Add the given term to the CC *)

  val assert_eq : t -> CurryfiedTerm.t -> CurryfiedTerm.t -> t
    (** Assert that the two terms are equal (may raise Inconsistent) *)

  val assert_diff : t -> CurryfiedTerm.t -> CurryfiedTerm.t -> t
    (** Assert that the two given terms are distinct (may raise Inconsistent) *)

  type action =
    | AssertEq of CurryfiedTerm.t * CurryfiedTerm.t
    | AssertDiff of CurryfiedTerm.t * CurryfiedTerm.t
    (** Action that can be performed on the CC *)

  val assert_action : t -> action -> t

  val eq : t -> CurryfiedTerm.t -> CurryfiedTerm.t -> bool
    (** Check whether the two terms are equal *)

  val can_eq : t -> CurryfiedTerm.t -> CurryfiedTerm.t -> bool
    (** Check whether the two terms can be equal *)

  val iter_equiv_class : t -> CurryfiedTerm.t -> (CurryfiedTerm.t -> unit) -> unit
    (** Iterate on terms that are congruent to the given term *)

  val explain : t -> CurryfiedTerm.t -> CurryfiedTerm.t -> action list
    (** Explain why those two terms are equal (they must be) *)
end
