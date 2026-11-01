/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Ring.Power
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Equality of powers at finite greatest common divisors

In a reduced ring, equality of powers at the greatest common divisor of a finite family of natural
exponents is equivalent to equality of powers at each exponent in the family.
-/

@[expose] public section

universe u v

/-- In a reduced ring, two elements have equal powers at the greatest common divisor of a finite
family of natural exponents if and only if they have equal powers at every exponent
in the family. -/
theorem IsReduced.pow_finset_gcd_eq_pow_finset_gcd_iff
    {R : Type u} {ι : Type v} [Ring R] [IsReduced R]
    (x y : R) (s : Finset ι) (e : ι → Nat) :
    x ^ (s.gcd e) = y ^ (s.gcd e) ↔ ∀ i ∈ s, x ^ (e i) = y ^ (e i) := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp [Finset.gcd_empty]
  | cons i s hi ih =>
      rw [Finset.gcd_cons hi, gcd_eq_nat_gcd,
        IsReduced.pow_gcd_eq_pow_gcd_iff, ih]
      simp
