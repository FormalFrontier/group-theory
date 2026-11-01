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

For a finite index type, a unital ring homomorphism to a nontrivial semiring
without zero divisors sends exactly one supported coordinate unit to one.

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

namespace RingHomClass

variable {ι : Type u} {R : ι → Type v} {S : Type w} {Γ : Type z}
variable [Finite ι] [DecidableEq ι] [∀ i, NonAssocSemiring (R i)]
variable [NonAssocSemiring S] [Nontrivial S] [NoZeroDivisors S]
variable [FunLike Γ (∀ i, R i) S] [RingHomClass Γ (∀ i, R i) S]

/-- A unital ring homomorphism from a finite product to a nontrivial semiring
without zero divisors sends exactly one supported coordinate unit to one.
Neither the source fibres nor the target need associative multiplication. -/
theorem existsUnique_map_single_one_eq_one (f : Γ) :
    ∃! i : ι, f (Pi.single i (1 : R i)) = (1 : S) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hdecomp : (∑ i, Pi.single i (1 : R i)) = (1 : ∀ i, R i) := by
    funext i
    have heval := map_sum (Pi.evalRingHom R i)
      (fun j => Pi.single j (1 : R j)) Finset.univ
    simp only [Pi.evalRingHom_apply] at heval
    rw [heval, Finset.sum_pi_single]
    simp
  have hsum : ∑ i, f (Pi.single i (1 : R i)) = (1 : S) := by
    rw [← map_sum, hdecomp, map_one]
  have horth (i j : ι) (hij : i ≠ j) :
      f (Pi.single i (1 : R i)) * f (Pi.single j (1 : R j)) = 0 := by
    rw [MulHomClass.single_one_mul_apply]
    simp [hij]
  obtain ⟨i, hi⟩ : ∃ i, f (Pi.single i (1 : R i)) ≠ 0 := by
    by_contra h
    have hz (i : ι) : f (Pi.single i (1 : R i)) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    exact zero_ne_one (by simpa only [hz, Finset.sum_const_zero] using hsum)
  have hzero (j : ι) (hji : j ≠ i) : f (Pi.single j (1 : R j)) = 0 :=
    (eq_zero_or_eq_zero_of_mul_eq_zero (horth i j hji.symm)).resolve_left hi
  have hi_one : f (Pi.single i (1 : R i)) = (1 : S) := by
    rw [← hsum]
    symm
    exact Finset.sum_eq_single i (fun j _ hji => hzero j hji) (by simp)
  refine ⟨i, hi_one, ?_⟩
  intro j hj
  by_contra hji
  exact one_ne_zero (hj.symm.trans (hzero j hji))

end RingHomClass
