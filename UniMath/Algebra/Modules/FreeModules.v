

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.Lists.

(* Define the free module on 'n' generators. *)
Section FreeModuleOnType.

Context (R' : rng) (n : nat).

Definition R := pr1 (pr1 R').

Definition plus_R := pr1 (pr2 (pr1 R')).
Definition times_R := pr2 (pr2 (pr1 R')).
Definition plus_R_is_abgrop : isabgrop plus_R := rngop1axs R'.
Definition zero_R : R := pr1 (pr2 (pr1 (pr1 plus_R_is_abgrop))).
Definition zero_R_is_unit :  isunit plus_R zero_R := pr2 (pr2 (pr1 (pr1 plus_R_is_abgrop))).

Definition underlying_type : UU
  := iterprod n R.

Definition F : UU := underlying_type.

Definition plus_F : F -> F -> F.
Proof.


  intros f g s.
  exact (plus_R (f s) (g s)).
Defined.

Definition zero_F : F := λ x, zero_R.
Definition zero_F_is_unit : isunit plus_F zero_F.
Proof.
  apply dirprodpair.
  - intros f.
    apply funextfun.
    intros x.
    exact ((pr1 zero_R_is_unit) (f x)).
  - intros f.
    apply funextfun.
    intros x.
    exact ((pr2 zero_R_is_unit) (f x)).
Defined.

Definition plus_F_is_assoc : isassoc plus_F.
Proof.
  intros f g h.
  apply funextfun.
  intros x.
  exact ((pr1 (pr1 (pr1 plus_R_is_abgrop))) _ _ _).
Defined.

Definition plus_F_is_comm : iscomm plus_F.
Proof.
  intros f g. apply funextfun. intros x.
  apply (pr2 plus_R_is_abgrop).
Defined.

Definition plus_F_is_abgrop : isabgrop plus_F.
Proof.
  refine (dirprodpair _ _).
  - refine


End FreeMonoidOnType.