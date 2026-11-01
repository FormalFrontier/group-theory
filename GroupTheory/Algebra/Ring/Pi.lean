/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Zero images of finite-support elements in products

A nonunital ring homomorphism from a dependent product sends a finite-support
element to zero exactly when it sends each of its zero-off coordinate insertions
to zero. The index type need not be finite, and the target need not have a unit
or associative multiplication.

## References

The proof uses Mathlib's finite sums, set finiteness and dependent Pi APIs,
together with multiplicative coordinate recovery.
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace NonUnitalRingHomClass

variable {ι : Type u} {R : ι → Type v} {S : Type w} {Γ : Type z}
variable [∀ i, NonAssocSemiring (R i)] [NonUnitalNonAssocSemiring S]
variable [DecidableEq ι] [FunLike Γ (∀ i, R i) S]
variable [NonUnitalRingHomClass Γ (∀ i, R i) S]

/-- A finite-support element of a dependent product has zero image if and only if
each of its zero-off coordinate insertions has zero image. Source units recover
the coordinate images, while finite additive decomposition gives the converse. -/
theorem map_eq_zero_iff_single_of_finite_support
    (f : Γ) (x : ∀ i, R i) (hx : Set.Finite {i | x i ≠ 0}) :
    f x = 0 ↔ ∀ i, f (Pi.single i (x i)) = 0 := by
  constructor
  · intro h i
    rw [← MulHomClass.single_one_mul_apply f i x, h, mul_zero]
  · intro h
    have hsum : (∑ i ∈ hx.toFinset, Pi.single i (x i)) = x := by
      funext i
      have heval := map_sum (Pi.evalNonUnitalRingHom R i)
        (fun j => Pi.single j (x j)) hx.toFinset
      simp only [Pi.evalNonUnitalRingHom_apply] at heval
      rw [heval, Finset.sum_pi_single]
      by_cases hi : x i = 0 <;> simp [hx.mem_toFinset, hi]
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero fun i _ => h i

end NonUnitalRingHomClass
