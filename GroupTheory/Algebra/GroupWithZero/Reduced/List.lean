/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Algebra.GroupWithZero.Reduced
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Positive powers in ordered zero products

In a reduced monoid with zero, replacing each occurrence in an ordered list by a positive power
preserves whether its product is zero. Exponents may vary between equal entries.

The argument uses Mathlib's relational product theorem and the scalar annihilator API for reduced
monoids. No commutativity, cancellation, absence of zero divisors or nontriviality is required.
-/

@[expose] public section

universe u

/-- Replacing each occurrence in a list by an independently chosen positive power preserves whether
the ordered product is zero. -/
theorem List.Forall₂.prod_eq_zero_iff_of_pow
    {M : Type u} [MonoidWithZero M] [IsReduced M]
    {l l' : List M}
    (h : List.Forall₂
      (fun a b : M => ∃ n : ℕ, n ≠ 0 ∧ b = a ^ n) l l') :
    l'.prod = 0 ↔ l.prod = 0 := by
  have hprod : ∀ p : M, p * l'.prod = 0 ↔ p * l.prod = 0 := by
    refine List.rel_prod
      (R := fun a b : M => ∀ p : M, p * b = 0 ↔ p * a = 0)
      (fun _ => Iff.rfl) ?_ ?_
    · intro a b hab c d hcd p
      calc
        p * (b * d) = 0 ↔ (p * b) * d = 0 := by rw [mul_assoc]
        _ ↔ (p * b) * c = 0 := hcd (p * b)
        _ ↔ c * (p * b) = 0 := IsReduced.mul_eq_zero_comm
        _ ↔ (c * p) * b = 0 := by rw [mul_assoc]
        _ ↔ (c * p) * a = 0 := hab (c * p)
        _ ↔ c * (p * a) = 0 := by rw [mul_assoc]
        _ ↔ (p * a) * c = 0 := IsReduced.mul_eq_zero_comm
        _ ↔ p * (a * c) = 0 := by rw [mul_assoc]
    · refine List.Forall₂.imp ?_ h
      intro a b hab p
      rcases hab with ⟨n, hn, rfl⟩
      exact mul_pow_eq_zero_iff hn
  simpa only [one_mul] using hprod 1
