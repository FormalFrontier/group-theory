/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
import GroupTheory.Algebra.BigOperators.Ring.Finset

/-!
# Nilpotence of finite orthogonal sums

A finite sum of pairwise orthogonal elements of a semiring is nilpotent if and only if
all its summands are nilpotent. No commutativity of the semiring is required.
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
