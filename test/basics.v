Require Import zenon.
Require Import zenon_induct.
Require Import zenon_focal.
Require Export Bool.
Require Export ZArith.
Open Scope Z_scope.
Require Export Reals.
Require Export Ascii.
Require Export String.
Require Export List.
Require Export Recdef.
Require Export coq_builtins.

Definition int__t :=  Z .

Definition unit__t :=  coq_builtins.bi__unit .

Definition float__t :=  R .

Definition char__t :=  ascii .

Definition string__t :=  string .

Definition bool__t :=  bool .

Definition list__t (__var_a : Set) :=  (List.list __var_a) .

Let focalize_error (__var_a : Set) : string__t -> __var_a :=
   coq_builtins.focalize_error .

Let _amper__amper_ : bool__t -> bool__t -> bool__t :=
   coq_builtins.bi__and_b .

Let _bar__bar_ : bool__t -> bool__t -> bool__t :=  coq_builtins.bi__or_b .

Let _tilda__tilda_ : bool__t -> bool__t :=  coq_builtins.bi__not_b .

Let _bar__lt__gt__bar_ : bool__t -> bool__t -> bool__t :=
   coq_builtins.bi__xor_b .

Let pair (__var_a : Set) (__var_b : Set) (x : __var_b) (y : __var_a) :
  ((__var_b * __var_a)%type) := (x, y).

Let fst (__var_a : Set) (__var_b : Set) (x : ((__var_b * __var_a)%type)) :
  __var_b := match x with
              | (v, _) =>
                  v
              end.

Let snd (__var_a : Set) (__var_b : Set) (x : ((__var_a * __var_b)%type)) :
  __var_b := match x with
              | (_, v) =>
                  v
              end.

Let _hat_ : string__t -> string__t -> string__t :=
   fun (x : string__t) (y : string__t) => coq_builtins.___a_string .

Let _lt__hat_ : string__t -> string__t -> bool__t :=
   fun (x : string__t) (y : string__t) => true .

Let _equal_0x : int__t -> int__t -> bool__t :=  coq_builtins.bi__int_eq .

Let _lt_0x : int__t -> int__t -> bool__t :=  coq_builtins.bi__int_lt .

Let _lt__equal_0x : int__t -> int__t -> bool__t :=  coq_builtins.bi__int_leq .

Let _gt__equal_0x : int__t -> int__t -> bool__t :=  coq_builtins.bi__int_geq .

Let _gt_0x : int__t -> int__t -> bool__t :=  coq_builtins.bi__int_gt .

Let _plus_ : int__t -> int__t -> int__t :=  coq_builtins.bi__int_plus .

Let _dash_ : int__t -> int__t -> int__t :=  coq_builtins.bi__int_minus .

Let _tilda_0x : int__t -> int__t :=  coq_builtins.bi__int_opposite .

Let _star_ : int__t -> int__t -> int__t :=  coq_builtins.bi__int_mult .

Let _slash_ : int__t -> int__t -> int__t :=  coq_builtins.bi__int_div .

Let _percent_ : int__t -> int__t -> int__t :=  coq_builtins.bi__int_mod .

Let succ0x (x : int__t) : int__t := (_plus_ x 1).

Let pred0x (x : int__t) : int__t := (_dash_ x 1).

Let max0x : int__t -> int__t -> int__t :=  coq_builtins.bi__int_max .

Let min0x : int__t -> int__t -> int__t :=  coq_builtins.bi__int_min .

Let abs0x : int__t -> int__t :=  coq_builtins.bi__int_abs .

Let string_of_int : int__t -> string__t :=
   fun (x : int__t) => coq_builtins.___a_string .

Let int_of_string : string__t -> int__t :=  fun (x : string__t) => 42 .

Let _equal_ (__var_a : Set) : __var_a -> __var_a -> bool__t :=
   coq_builtins.bi__syntactic_equal __var_a .

Let syntactic_equal (__var_a : Set) : __var_a -> __var_a -> bool__t :=
  _equal_ _.

Let print_int : int__t -> unit__t :=  fun (x : int__t) => coq_builtins.Void .

Let print_newline : unit__t -> unit__t :=
   fun (x : unit__t) => coq_builtins.Void .

Let print_string : string__t -> unit__t :=
   fun (x : string__t) => coq_builtins.Void .


(* From species basics#*Toplevel*. *)
Theorem beq_refl :
  forall __var_a : Set, forall x : __var_a, Is_true ((_equal_ _ x x)).
 apply syntactic_equal_refl. Qed. 



(* From species basics#*Toplevel*. *)
Theorem beq_symm :
  forall __var_a : Set, forall x  y : __var_a,
    Is_true ((_equal_ _ x y)) -> Is_true ((_equal_ _ y x)).
 apply syntactic_equal_sym. Qed. 



(* From species basics#*Toplevel*. *)
Theorem beq_trans :
  forall __var_a : Set, forall x  y  z : __var_a,
    Is_true ((_equal_ _ x y)) ->
      Is_true ((_equal_ _ y z)) -> Is_true ((_equal_ _ x z)).
 apply syntactic_equal_trans. Qed. 



(* From species basics#*Toplevel*. *)
Theorem int_le_not_gt :
  forall x  y : int__t,
    Is_true (((_lt__equal_0x x y))) -> ~Is_true (((_gt_0x x y))).

      intros x y; unfold _lt__equal_0x, _gt_0x  in |- *.
      unfold bi__int_leq , bi__int_gt.
      elim (Z_le_dec x y).
      intros H.
      intros b; clear b.
      elim (Z_gt_dec x y).
      intros H1; absurd (x > y)%Z.
      apply Zle_not_gt; trivial.
      trivial.
      compute in |- *; trivial.
      compute in |- *; trivial.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_lt_le_trans :
  forall x  y  z : int__t,
    Is_true ((_lt_0x x y)) ->
      Is_true ((_lt__equal_0x y z)) -> Is_true ((_lt_0x x z)).

      intros x y z.
      unfold _lt_0x, _lt__equal_0x,
             bi__int_lt, bi__int_leq in |- *.
      elim (Z_lt_dec x y).
      elim (Z_le_dec y z).
      intros Hle Hlt foo bar; clear foo bar.
      elim (Z_lt_dec x z).
      intros H; compute in |- *; trivial.
      intros H; absurd (x < z)%Z; trivial.
      apply (Zlt_le_trans x y z); trivial.
      intros b a H Habs; compute in |- *; contradiction.
      intros b H; compute in H; contradiction.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_le_refl :
  forall x  y : int__t,
    Is_true ((_equal_ _ x y)) -> Is_true ((_lt__equal_0x x y)).
(* Proof was flagged as assumed *)
apply coq_builtins.magic_prove.
Qed.



(* From species basics#*Toplevel*. *)
Theorem int_le_antisymm :
  forall x  y : int__t,
    Is_true ((_lt__equal_0x x y)) ->
      Is_true ((_lt__equal_0x y x)) -> Is_true ((_equal_ _ x y)).

      intros x y.
      unfold _lt__equal_0x, bi__int_leq in |- *.
      elim (Z_le_dec x y); elim (Z_le_dec y x).
      intros H1 H2.
      intros b c; clear b c.
      replace x with y.
      eapply beq_refl.
      apply Zle_antisym; trivial.
      intros b a H; clear H a.
      compute in |- *; intros Habs; eapply False_ind; trivial.
      intros a b Habs H; clear H a; compute in Habs; eapply False_ind; trivial.
      intros a b Habs H; clear H a; compute in Habs; eapply False_ind; trivial.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_le_trans :
  forall x  y  z : int__t,
    Is_true ((_lt__equal_0x x y)) ->
      Is_true ((_lt__equal_0x y z)) -> Is_true ((_lt__equal_0x x z)).

      unfold _lt__equal_0x, bi__int_leq in |- *; intros x y z H1 H2.
      apply dec_IsTrue. cut (x <= y)%Z. cut (y <= z)%Z.
      eauto with zarith.
      eapply IsTrue_dec. apply H2.
      eapply IsTrue_dec; apply H1.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_lt_irrefl :
  forall x  y : int__t, Is_true ((_lt_0x x y)) -> ~Is_true ((_equal_ _ x y)).
(* Proof was flagged as assumed *)
apply coq_builtins.magic_prove.
Qed.



(* From species basics#*Toplevel*. *)
Theorem int_0_plus :
  forall x  y : int__t,
    Is_true ((_equal_ _ x 0)) -> Is_true ((_equal_ _ (_plus_ x y) y)).

      unfold bi__int_plus in |- *; intros x y Hxz;
      unfold _equal_, syntactic_equal;
      apply EQ_syntactic_equal; replace x with 0%Z; eauto with zarith.
      symmetry  in |- *.
      apply decidable.
      apply Z_eq_dec. assumption.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_lt_le_S :
  forall x  y : int__t,
    Is_true ((_lt_0x x y)) -> Is_true ((_lt__equal_0x (_plus_ x 1) y)).

      unfold _lt_0x, _lt__equal_0x,
        _plus_ in |- *; intros x y Hlt;
      unfold bi__int_lt, bi__int_leq, bi__int_plus;
      apply dec_IsTrue; fold (Zsucc x) in |- *; apply Zlt_le_succ;
      trivial. exact (IsTrue_dec Hlt).
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_plus_assoc :
  forall x  y  z : int__t,
    Is_true ((_equal_ _ (_plus_ ((_plus_ x y)) z) (_plus_ x ((_plus_ y z))))).

      intros x y z;
      unfold _equal_, syntactic_equal;
      apply EQ_syntactic_equal; auto with zarith.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_plus_commute :
  forall x  y : int__t, Is_true ((_equal_ _ (_plus_ x y) (_plus_ y x))).

      intros x y;
      unfold _equal_, syntactic_equal;
      apply EQ_syntactic_equal;
      auto with zarith.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_plus_plus :
  forall x  y  z  t : int__t,
    Is_true ((_equal_ _ x y)) ->
      Is_true ((_equal_ _ z t)) ->
        Is_true ((_equal_ _ (_plus_ x z) (_plus_ y t))).

      intros x y z t H1 H2;
      unfold _equal_;
      apply EQ_syntactic_equal; replace y with x. replace t with z. reflexivity.
      apply decidable. apply Z_eq_dec. assumption.
      apply decidable. apply Z_eq_dec. assumption.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_le_plus_plus :
  forall x  y  z  t : int__t,
    Is_true ((_lt__equal_0x x y)) ->
      Is_true ((_lt__equal_0x z t)) ->
        Is_true ((_lt__equal_0x (_plus_ x z) (_plus_ y t))).

      unfold _plus_, _lt__equal_0x in |- *; intros x y z t H1 H2;
      unfold bi__int_leq, bi__int_plus, bi__int_plus;
      apply dec_IsTrue; apply Zplus_le_compat;
      [ exact (IsTrue_dec H1) | exact (IsTrue_dec H2) ].
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_min_le :
  forall x  y  z : int__t,
    (Is_true ((_lt__equal_0x z x)) /\ Is_true ((_lt__equal_0x z y))) ->
      Is_true ((_lt__equal_0x z (min0x x y))).

      intros x y z H; elim H; intros H1 H2; clear H;
      unfold min0x in |- *;
      unfold bi__int_min;
      elim (Z_lt_dec x y);
      intros H; trivial.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_min_le2 :
  forall x  y  z : int__t,
    Is_true ((_lt__equal_0x z (min0x x y))) ->
      (Is_true ((_lt__equal_0x z x)) /\ Is_true ((_lt__equal_0x z y))).

      intros x y z; unfold min0x in |- *.
      unfold bi__int_min.
      case (Z_lt_dec x y); intros H1 H2; split; trivial.
      apply int_le_trans with x; trivial.
      unfold _lt__equal_0x, bi__int_leq;
      apply dec_IsTrue; apply Zlt_le_weak; trivial.
      apply int_le_trans with y; trivial.
      unfold _lt__equal_0x, bi__int_leq; apply dec_IsTrue.
      elim (Zle_or_lt y x); trivial.   intros Habs; absurd (x < y)%Z; trivial.
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_plus_minus :
  forall x  y  z : int__t,
    Is_true ((_equal_ _ (_plus_ x y) z)) ->
      Is_true (((_equal_ _ y (_dash_ z x)))).

      intros x y z; unfold syntactic_equal in |- *;
      intros H;
      unfold bi__int_minus, _equal_, syntactic_equal;
      apply EQ_syntactic_equal; apply Zplus_minus_eq;
      symmetry  in |- *; apply (decidable _ _ _ (Z_eq_dec (x + y) z) H).
      Qed.
    



(* From species basics#*Toplevel*. *)
Theorem int_minus_plus :
  forall x  y  z : int__t,
    Is_true ((_equal_ _ (_dash_ x y) z)) ->
      Is_true ((_equal_ _ x (_plus_ y z))).

      intros x y z; unfold syntactic_equal in |- *;
      intros H;
      unfold bi__int_minus, _equal_, syntactic_equal;
      apply EQ_syntactic_equal; rewrite <- (Zplus_minus y x);
      apply Zplus_eq_compat; trivial; apply decidable. apply Z_eq_dec. assumption.
      Qed.
    


Module Basic_object.
  Record Basic_object : Type :=
    mk_record {
    rf_T :> Set ;
    (* From species basics#Basic_object. *)
    rf_parse : string__t -> rf_T ;
    (* From species basics#Basic_object. *)
    rf_print : rf_T -> string__t
    }.
  
  Definition parse (abst_T : Set) (_x : string__t) : abst_T :=
    (focalize_error _ coq_builtins.___a_string).
  Definition print (abst_T : Set) (_x : abst_T) : string__t :=
    coq_builtins.___a_string.
  
End Basic_object.

Inductive partiel__t (__var_a : Set) : Set := 
  | Failed : ((partiel__t __var_a))
  | Unfailed : (__var_a -> (partiel__t __var_a)).

Let is_failed (__var_a : Set) (x : (partiel__t __var_a)) : bool__t :=
  match x with
   | Failed  =>
       true
   | Unfailed _ =>
       false
   end.

Let non_failed (__var_a : Set) (x : (partiel__t __var_a)) : __var_a :=
  match x with
   | Failed  =>
       (focalize_error _ coq_builtins.___a_string)
   | Unfailed a =>
       a
   end.

