/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Pairwise
public import GroupTheory.Algebra.GroupWithZero.Nilpotent
import GroupTheory.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Nilpotence bounds for finite sums

A finite sum of pairwise orthogonal elements of a semiring is nilpotent if and only if
all its summands are nilpotent. Its nilpotency class is at most the maximum of the
supported classes and the class of zero, which accounts for empty support.
No commutativity of the semiring is required.

For a finite pairwise commuting family with supported equations `f i ^ n i = 0`,
`Finset.sum_pow_eq_zero_of_pairwise_commute` gives
`(∑ i ∈ s, f i) ^ (1 + ∑ i ∈ s, (n i - 1)) = 0`.
The exponents vary independently, and subtraction is natural-number subtraction.
No positivity or nontriviality hypothesis is needed: empty support gives exponent one,
and a supported zero exponent forces the semiring to be trivial.

This module also re-exports `SemiconjBy.nilpotencyClass_le_add_one`. A supported
left row of orthogonality gives `SemiconjBy (f i) (∑ j ∈ s, f j) (f i)` by
`Finset.mul_sum` and `Finset.sum_eq_single`. If the sum is nilpotent, the generic
bound then gives `nilpotencyClass (f i) ≤ nilpotencyClass (∑ j ∈ s, f j) + 1`.

## References

The commuting power bound uses Mathlib's binary quantitative theorem
`Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero` from the nilpotent theory
formalized by Oliver Nash.
-/

@[expose] public section

open scoped BigOperators

universe u v

/-- A finite sum of pairwise orthogonal elements is nilpotent if and only if every
summand is nilpotent. -/
theorem Finset.isNilpotent_sum_iff_of_pairwise_mul_eq_zero
    {R : Type u} [Semiring R]
    {ι : Type v} (s : Finset ι) (f : ι → R)
    (h : (s : Set ι).Pairwise (fun i j => f i * f j = 0)) :
    IsNilpotent (∑ i ∈ s, f i) ↔ ∀ i ∈ s, IsNilpotent (f i) := by
  classical
  constructor
  · rintro ⟨n, hn⟩ i hi
    have hsum : (∑ j ∈ s, f j) ^ (n + 1) = 0 := by
      rw [pow_succ, hn, zero_mul]
    have hpowers : (∑ j ∈ s, f j ^ (n + 1)) = 0 :=
      (Finset.sum_pow_eq_sum_pow_of_pairwise_mul_eq_zero s f h
        (Nat.succ_ne_zero n)).symm.trans hsum
    refine ⟨n + 2, ?_⟩
    calc
      f i ^ (n + 2) = f i * f i ^ (n + 1) := pow_succ' (f i) (n + 1)
      _ = f i * (∑ j ∈ s, f j ^ (n + 1)) := by
        rw [Finset.mul_sum]
        symm
        apply Finset.sum_eq_single i
        · intro j hj hji
          rw [pow_succ', ← mul_assoc, h hi hj hji.symm, zero_mul]
        · intro hnot
          exact (hnot hi).elim
      _ = 0 := by rw [hpowers, mul_zero]
  · intro hall
    -- Construct a positive common killing exponent without commuting any factors.
    have common : ∀ t : Finset ι, (∀ i ∈ t, IsNilpotent (f i)) →
        ∃ n : ℕ, n ≠ 0 ∧ ∀ i ∈ t, f i ^ n = 0 := by
      intro t
      refine Finset.cons_induction_on t ?_ ?_
      · intro _
        refine ⟨1, Nat.one_ne_zero, ?_⟩
        intro i hi
        simp at hi
      · intro a t _hat ih ht
        obtain ⟨m, hm⟩ := ht a (Finset.mem_cons.mpr (Or.inl rfl))
        obtain ⟨n, _hn, hnt⟩ :=
          ih (fun i hi => ht i (Finset.mem_cons.mpr (Or.inr hi)))
        refine ⟨m + n + 1, Nat.succ_ne_zero (m + n), ?_⟩
        intro i hi
        rcases Finset.mem_cons.mp hi with rfl | hi
        · rw [pow_succ, pow_add, hm, zero_mul, zero_mul]
        · rw [Nat.add_comm m n, pow_succ, pow_add, hnt i hi, zero_mul, zero_mul]
    obtain ⟨n, hn, hfn⟩ := common s hall
    refine ⟨n, ?_⟩
    rw [Finset.sum_pow_eq_sum_pow_of_pairwise_mul_eq_zero s f h hn]
    exact Finset.sum_eq_zero (fun i hi => hfn i hi)

namespace Finset

/-- The nilpotency class of an orthogonal finite sum is bounded by the supported classes,
with the class of zero accounting for empty support. -/
theorem nilpotencyClass_sum_le_of_pairwise_mul_eq_zero
    {R : Type u} [Semiring R] {ι : Type v} (s : Finset ι) (f : ι → R)
    (h : (s : Set ι).Pairwise (fun i j => f i * f j = 0)) :
    nilpotencyClass (∑ i ∈ s, f i) ≤
      max (nilpotencyClass (0 : R)) (s.sup (fun i => nilpotencyClass (f i))) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : Subsingleton R := hR
    calc
      nilpotencyClass (∑ i ∈ s, f i) = 0 :=
        _root_.nilpotencyClass_eq_zero_of_subsingleton
      _ ≤ _ := Nat.zero_le _
  · let : Nontrivial R := hR
    by_contra hle
    have hlt :
        max (nilpotencyClass (0 : R)) (s.sup (fun i => nilpotencyClass (f i))) <
          nilpotencyClass (∑ i ∈ s, f i) := lt_of_not_ge hle
    have hsum : IsNilpotent (∑ i ∈ s, f i) :=
      _root_.isNilpotent_of_pos_nilpotencyClass
        (lt_of_le_of_lt (Nat.zero_le _) hlt)
    have hf : ∀ i ∈ s, IsNilpotent (f i) :=
      (Finset.isNilpotent_sum_iff_of_pairwise_mul_eq_zero s f h).mp hsum
    cases hc : nilpotencyClass (∑ i ∈ s, f i) with
    | zero =>
        simp only [hc, Nat.not_lt_zero] at hlt
    | succ n =>
        have hmax :
            max (nilpotencyClass (0 : R)) (s.sup (fun i => nilpotencyClass (f i))) ≤ n := by
          simpa only [hc, Nat.lt_succ_iff] using hlt
        have hn : n ≠ 0 := by
          have hone : 1 ≤ n := by
            simpa only [_root_.nilpotencyClass_zero] using
              (le_trans (le_max_left (nilpotencyClass (0 : R))
                (s.sup (fun i => nilpotencyClass (f i)))) hmax)
          exact ne_of_gt hone
        apply _root_.pow_pred_nilpotencyClass hsum
        rw [hc, Nat.succ_sub_one,
          Finset.sum_pow_eq_sum_pow_of_pairwise_mul_eq_zero s f h hn]
        apply Finset.sum_eq_zero
        intro i hi
        have hbound : nilpotencyClass (f i) ≤ n :=
          le_trans (Finset.le_sup (f := fun j => nilpotencyClass (f j)) hi)
            ((le_max_right _ _).trans hmax)
        calc
          f i ^ n = f i ^ (n - nilpotencyClass (f i) + nilpotencyClass (f i)) := by
            rw [Nat.sub_add_cancel hbound]
          _ = 0 := by
            rw [pow_add, _root_.pow_nilpotencyClass (hf i hi), mul_zero]

/-- A finite sum of pairwise commuting elements vanishes at one plus the sum of the
predecessors of their individual vanishing exponents. The exponents need not be positive. -/
theorem sum_pow_eq_zero_of_pairwise_commute
    {R : Type u} [Semiring R] {ι : Type v}
    (s : Finset ι) (f : ι → R) (n : ι → ℕ)
    (hpow : ∀ i ∈ s, (f i) ^ n i = 0)
    (hcomm : (s : Set ι).Pairwise (fun i j => Commute (f i) (f j))) :
    (∑ i ∈ s, f i) ^ (1 + ∑ i ∈ s, (n i - 1)) = 0 := by
  classical
  revert hpow hcomm
  refine Finset.cons_induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a t hat ih hpow hcomm
    have htail : (∑ i ∈ t, f i) ^ (1 + ∑ i ∈ t, (n i - 1)) = 0 :=
      ih (fun i hi => hpow i (Finset.mem_cons.mpr (Or.inr hi))) (by
        intro i hi j hj hij
        exact hcomm (Finset.mem_cons.mpr (Or.inr hi))
          (Finset.mem_cons.mpr (Or.inr hj)) hij)
    have hsumcomm : Commute (f a) (∑ i ∈ t, f i) := by
      apply Commute.sum_right
      intro i hi
      exact hcomm (Finset.mem_cons.mpr (Or.inl rfl))
        (Finset.mem_cons.mpr (Or.inr hi)) (fun hai => hat (hai.symm ▸ hi))
    simp only [Finset.sum_cons]
    apply Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hsumcomm
      (hpow a (Finset.mem_cons.mpr (Or.inl rfl))) htail
    -- The binary threshold also holds when the new exponent is zero.
    omega

end Finset
