/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Monoid

/-!
# Additive units, zero sums, and multiplicative images

Multiplication by an additively invertible element annihilates an element absorbed
by addition. In a semiring this gives a quantitative nilpotence criterion:
`a ^ n + c = c` implies `a ^ (n + 1) = 0` when `a` is an additive unit.
Neither multiplication commutativity nor additive cancellation is required.

In a nonunital, nonassociative semiring, two elements with zero sum have equal
self-products. A multiplication-preserving function from such a semiring to a
monoid therefore sends a zero-sum pair to values that are units simultaneously,
without requiring preservation of addition, zero or one.

## References

The self-product identity generalizes the zero-sum argument used in
[valuation-integers](https://github.com/FormalFrontier/valuation-integers).
The image-unit equivalence uses Mathlib's `isUnit_mul_self_iff`.
-/

@[expose] public section

universe u

namespace IsAddUnit

/-- An additive unit annihilates every element absorbed by addition. -/
theorem mul_eq_zero_of_add_eq {A : Type u} [NonUnitalNonAssocSemiring A]
    {a b c : A} (ha : IsAddUnit a) (h : b + c = c) : a * b = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hu : (u : A) + ((-u : AddUnits A) : A) = 0 :=
    congrArg (fun z : AddUnits A => (z : A)) (add_neg_cancel u)
  have hc : (u : A) * c + ((-u : AddUnits A) : A) * c = 0 := by
    rw [← add_mul, hu, zero_mul]
  calc
    (u : A) * b = (u : A) * b + 0 := (add_zero _).symm
    _ = ((u : A) * b + (u : A) * c) + ((-u : AddUnits A) : A) * c := by
      rw [add_assoc, hc, add_zero]
    _ = (u : A) * c + ((-u : AddUnits A) : A) * c := by rw [← mul_add, h]
    _ = 0 := hc

/-- An absorbed power of an additive unit vanishes after one further multiplication.
The exponent `n` may be zero. -/
theorem pow_succ_eq_zero_of_add_eq {A : Type u} [Semiring A]
    {a c : A} (ha : IsAddUnit a) {n : ℕ} (h : a ^ n + c = c) :
    a ^ (n + 1) = 0 := by
  rw [pow_succ']
  exact ha.mul_eq_zero_of_add_eq h

end IsAddUnit

universe v w

/-- Two elements with zero sum have equal self-products in a nonunital,
nonassociative semiring. -/
theorem mul_self_eq_mul_self_of_add_eq_zero
    {S : Type u} [NonUnitalNonAssocSemiring S] {a b : S}
    (h : a + b = 0) : a * a = b * b := by
  have ha : a * a + a * b = 0 := by rw [← mul_add, h, mul_zero]
  have hb : a * b + b * b = 0 := by rw [← add_mul, h, zero_mul]
  exact left_neg_eq_right_neg ha hb

namespace MulHomClass

/-- A multiplication-preserving function sends two elements with zero sum to
values that are units simultaneously. Preservation of addition, zero or one is
not required, and the source need not have a multiplicative identity or
associative multiplication. -/
theorem isUnit_apply_iff_of_add_eq_zero
    {S : Type u} {T : Type v} {F : Type w}
    [NonUnitalNonAssocSemiring S] [Monoid T]
    [FunLike F S T] [MulHomClass F S T]
    (μ : F) {a b : S} (h : a + b = 0) : IsUnit (μ a) ↔ IsUnit (μ b) := by
  have hsq : μ a * μ a = μ b * μ b := by
    simpa only [map_mul] using congrArg μ (mul_self_eq_mul_self_of_add_eq_zero h)
  rw [← isUnit_mul_self_iff (a := μ a), hsq, isUnit_mul_self_iff]

end MulHomClass
