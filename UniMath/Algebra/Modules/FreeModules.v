

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Algebra.Modules.Core.

(* Define the free module on 'n' generators. *)
Section FiniteRankFreeModule.

Context (R' : rng) (n : nat).

Definition R := pr1 (pr1 R').

Definition plus_R := pr1 (pr2 (pr1 R')).
Definition mult_R := pr2 (pr2 (pr1 R')).
Definition plus_R_is_abgrop : isabgrop plus_R := rngop1axs R'.
Definition zero_R : R := pr1 (pr2 (pr1 (pr1 plus_R_is_abgrop))).
Definition zero_R_is_unit :  isunit plus_R zero_R := pr2 (pr2 (pr1 (pr1 plus_R_is_abgrop))).
Definition plus_R_inv : R -> R := rnginv1.
Definition plus_R_is_linv : islinv plus_R zero_R plus_R_inv
  := grlinvax_is (pr1 plus_R_is_abgrop).
Definition plus_R_is_rinv : isrinv plus_R zero_R plus_R_inv
  := grrinvax_is (pr1 plus_R_is_abgrop).
Definition R_is_distr : isdistr plus_R mult_R := rngdistraxs R'.
Definition mult_R_is_monoidop : ismonoidop mult_R := rngop2axs R'.
Definition one_R : R := rngunel2.


(* define the underlying type of the free module
   as maps from the standard n-element set to R *)
Definition underlying_type : UU
  := stn n -> R.

Definition F : UU := underlying_type.

Definition plus_F : F -> F -> F.
Proof.
  intros f g i.
  exact (plus_R (f i) (g i)).
Defined.

Definition zero_F : F := λ i, zero_R.
Definition zero_F_is_unit : isunit plus_F zero_F.
Proof.
  apply dirprodpair.
  - intros f.
    apply funextfun.
    intros i.
    exact ((pr1 zero_R_is_unit) (f i)).
  - intros f.
    apply funextfun.
    intros i.
    exact ((pr2 zero_R_is_unit) (f i)).
Defined.

Definition plus_F_is_assoc : isassoc plus_F.
Proof.
  intros f g h.
  apply funextfun.
  intros i.
  use (rngassoc1 R').
Defined.

Definition plus_F_is_comm : iscomm plus_F.
Proof.
  intros f g. apply funextfun. intros i.
  apply (rngcomm1 R').
Defined.

Definition plus_F_inv : F -> F.
Proof.
  intros f.
  exact (λ x, plus_R_inv (f x)).
Defined.

Definition plus_F_is_abgrop : isabgrop plus_F.
Proof.
  apply mk_isabgrop.
  - use mk_isgrop.
    + apply dirprodpair.
      * exact plus_F_is_assoc.
      * exact (isunitalpair zero_F zero_F_is_unit).
    + use mk_invstruct.
      * exact plus_F_inv.
      * use mk_isinv.
        -- intros f. apply funextfun. intros i.
           use plus_R_is_linv.
        -- intros f. apply funextfun. intros i.
           use plus_R_is_rinv.
  - use plus_F_is_comm.
Defined.

Definition scalar_mult_F : R -> F -> F :=
  (λ r f, λ i, mult_R r (f i)).

Definition F_as_hSet : hSet.
Proof.
  use hSetpair.
  - use F.
  - use isaset_forall_hSet.
Defined.

Definition F_as_module : module R'.
Proof.
  use mult_to_module.
  - use abgrpair.
    + use (setwithbinoppair F_as_hSet plus_F).
    + use plus_F_is_abgrop.
  - use scalar_mult_F.
  - intros r f g. apply funextfun. intros i.
    use (pr1 R_is_distr).
  - intros r f g. apply funextfun. intros i.
    use (pr2 R_is_distr).
  - intros r r' f. apply funextfun. intros i.
    exact ((pr1 mult_R_is_monoidop) r r' (f i)).
  - intros f. apply funextfun. intros i.
    use rnglunax2.
Defined.

End FiniteRankFreeModule.