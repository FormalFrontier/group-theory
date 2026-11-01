/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Pairwise

/-!
# Powers of finite orthogonal sums

Positive powers of a finite sum of pairwise orthogonal elements are the sums of the
corresponding powers, even in a noncommutative semiring.
-/

@[expose] public section

open scoped BigOperators

universe u v

/-- A positive power of a finite sum of pairwise orthogonal elements is the sum of their
corresponding powers. -/
theorem Finset.sum_pow_eq_sum_pow_of_pairwise_mul_eq_zero
    {R : Type u} [Semiring R]
    {ι : Type v} (s : Finset ι) (f : ι → R)
    (h : (s : Set ι).Pairwise (fun i j => f i * f j = 0))
    {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ s, f i) ^ n = ∑ i ∈ s, f i ^ n := by
  classical
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    clear hn
    induction n with
    | zero => simp only [Nat.zero_add, pow_one]
    | succ n ih =>
      calc
        (∑ i ∈ s, f i) ^ (n + 1 + 1) =
            (∑ i ∈ s, f i ^ (n + 1)) * ∑ j ∈ s, f j := by
          rw [pow_succ, ih]
        _ = ∑ i ∈ s, ∑ j ∈ s, f i ^ (n + 1) * f j :=
          Finset.sum_mul_sum s s _ _
        _ = ∑ i ∈ s, f i ^ (n + 1 + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            (∑ j ∈ s, f i ^ (n + 1) * f j) = f i ^ (n + 1) * f i := by
              apply Finset.sum_eq_single i
              · intro j hj hji
                rw [pow_succ, mul_assoc, h hi hj hji.symm, mul_zero]
              · intro his
                exact (his hi).elim
            _ = f i ^ (n + 1 + 1) := (pow_succ (f i) (n + 1)).symm
