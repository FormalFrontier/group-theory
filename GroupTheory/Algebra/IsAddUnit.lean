/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Basic

/-!
# Additive units and absorption

Multiplication by an additively invertible element annihilates an element absorbed
by addition. In a semiring this gives a quantitative nilpotence criterion:
`a ^ n + c = c` implies `a ^ (n + 1) = 0` when `a` is an additive unit.
Neither multiplication commutativity nor additive cancellation is required.
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
