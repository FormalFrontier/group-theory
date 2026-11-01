/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Finset.Pairwise

/-!
# Zero sums of orthogonal families in reduced semirings

A finite family in a reduced semiring with pairwise zero products has zero sum if and only
if every summand is zero. Orthogonality is required only at distinct indices, and
multiplication need not be commutative.
-/

@[expose] public section

open scoped BigOperators

universe u v

/-- A finite sum of pairwise orthogonal elements in a reduced semiring is zero if and only
if every summand is zero. The pairwise hypothesis concerns distinct indices only. -/
theorem Finset.sum_eq_zero_iff_of_pairwise_mul_eq_zero
    {R : Type u} [Semiring R] [IsReduced R]
    {ι : Type v} (s : Finset ι) (f : ι → R)
    (h : (s : Set ι).Pairwise (fun i j => f i * f j = 0)) :
    (∑ i ∈ s, f i) = 0 ↔ ∀ i ∈ s, f i = 0 := by
  classical
  constructor
  · intro hs i hi
    apply sq_eq_zero_iff.mp
    rw [pow_two]
    calc
      f i * f i = ∑ j ∈ s, f i * f j := by
        symm
        exact Finset.sum_eq_single i
          (fun j hj hji => h hi hj hji.symm)
          (fun hni => (hni hi).elim)
      _ = f i * ∑ j ∈ s, f j := by rw [Finset.mul_sum]
      _ = 0 := by rw [hs, mul_zero]
  · intro hf
    exact Finset.sum_eq_zero hf
