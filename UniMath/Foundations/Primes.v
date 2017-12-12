Require Import UniMath.Foundations.NaturalNumbers.

Definition remainderzero_yields_factors (n m : nat) (b : n /+ m = 0) (_ : m ≠ 0) :
  n = (n / m) * m.
Proof.
  intros.
  assert (n = (n /+ m) + (n / m) * m).
  apply natdivremrule. assumption.
  rewrite b in H.
  rewrite natplusl0 in H.
  assumption.
Defined.

Eval compute in natdivrem 43 6.

Definition divisible (n m : nat) : bool.
Proof.
  intros. induction (n /+ m) as [| nonzero].
  - exact true.
  - exact false.
Defined.

Eval compute in divisible 41 7.
Eval compute in divisible 0 2.
Eval compute in divisible 0 0.
Eval compute in divisible 5 0.

Definition divisibility_yields_factors (n m : nat) (b : divisible n m = true) (_ : m ≠ 0) :
  ∑ k : nat, n = k * m.
Proof.
  intros. exists (n / m).
  pose (r := n /+ m).
  assert (p : r = n /+ m).
  apply idpath.
  induction r.
  - apply remainderzero_yields_factors.
    exact (!p). assumption.
  - assert (q : divisible n m = divisible n m). apply idpath.
    unfold divisible in q at 1.
    rewrite <- p in q. assert (false = true). exact (q @ b).
    contradicts nopathsfalsetotrue H.
Defined.


Definition natlthsum (n m k : nat) (le : k + m < n) : (k < n).
Proof.
  assert (le' : k ≤ k + m).
  apply natlehnplusnm.
  refine (natlehlthtrans _ _ _ _ _).
  exact le'.
  assumption.
Defined.

Definition summands_are_smaller  (n m k : nat) (m_nonzero : m ≠ 0) (eq : n = k + m) : (k < n).
Proof.
  induction m as [| m'].
  - contradicts (nat_neq_to_nopath m_nonzero) (idpath 0).
  - rewrite natplusnsm in eq.
    assert (le : n > k + m').
    rewrite eq.
    apply natlthnsn.
    apply (natlthsum n m' k).
    assumption.
Defined.

Definition factors_are_smaller (n m k : nat) (gr_n : 0 ≠ n) (gr_m : 1 < m) (is_factor : n = m * k) : (k < n).
Proof.
  intros.
  induction m as [| m' IHm'].
  - contradicts (negnatlthn0 1) gr_m.
  - induction m' as [| m'' IHm''].
    + contradicts (isirreflnatlth 1) gr_m.
    + assert (eq : n = k + (S m'') * k).
      rewrite multsnm in is_factor.
      assumption.
      refine (summands_are_smaller _ (S m'' * k) _ _ eq).
      apply natneq0andmult.
      * apply natneqsx0.
      * rewrite is_factor in gr_n. Search (_ ≠ 0).
        refine (natneq0andmultrinv _ _ (issymm_natneq _ _ gr_n)).
Defined.

Definition count_divisors_leq (n d : nat) : nat.
Proof.
  intros. induction d as [| d' IHd'].
  - exact 0.
  - induction (divisible n (S d')).
    + exact (S IHd').
    + exact IHd'.
Defined.

Eval compute in count_divisors_leq 5 2.
Eval compute in count_divisors_leq 5 5.
Eval compute in count_divisors_leq 17 12.
Eval compute in count_divisors_leq 24 50.
Eval compute in count_divisors_leq 1 1.
Eval compute in count_divisors_leq 0 0.

Definition prime (p : nat) : hProp :=
  hProppair (count_divisors_leq p p = 2) (isasetnat (count_divisors_leq p p) 2).

Eval cbv in prime 17.

Definition prime_decidable (p : nat) : decidable (prime p).
Proof.
  intros. apply isdeceqnat.
Defined.
