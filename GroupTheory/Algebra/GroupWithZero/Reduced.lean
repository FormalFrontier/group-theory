/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Positive-power annihilators in reduced monoids with zero

In a reduced monoid with zero, replacing either factor of a product by a positive
natural power does not change whether the product is zero. The simp lemmas
`pow_mul_eq_zero_iff` and `mul_pow_eq_zero_iff` preserve the order of the factors;
commutativity and absence of zero divisors are not required.

The proofs use Mathlib's square-zero criterion `sq_eq_zero_iff`, upward propagation
`pow_mul_eq_zero_of_le`, and the reducedness and power APIs for `MulOpposite`.
When the other factor is one, these specialize to Mathlib's `pow_eq_zero_iff`.
-/

@[expose] public section

universe u

/-- In a reduced monoid with zero, reversing the factors preserves a zero product. -/
theorem IsReduced.mul_eq_zero_comm {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} : a * b = 0 ↔ b * a = 0 := by
  have reverse (a b : M) (hab : a * b = 0) : b * a = 0 := by
    apply sq_eq_zero_iff.mp
    calc
      (b * a) ^ 2 = b * (a * b) * a := by simp only [pow_two, mul_assoc]
      _ = 0 := by rw [hab, mul_zero, zero_mul]
  exact ⟨reverse a b, reverse b a⟩

/-- A positive power has the same right annihilators as the element itself in a
reduced monoid with zero. Positivity is essential: the zeroth power is one.
Reducedness is essential already with `b = 1` and a nonzero square-zero element. -/
@[simp]
theorem pow_mul_eq_zero_iff {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} {m : ℕ} (hm : m ≠ 0) : a ^ m * b = 0 ↔ a * b = 0 := by
  have square_step (c : M) (h : a ^ 2 * c = 0) : a * c = 0 := by
    -- Two square-zero tests remove the repeated factor without commuting it past `c`.
    have haca : a * c * a = 0 := sq_eq_zero_iff.mp <| by
      calc
        (a * c * a) ^ 2 = a * c * (a ^ 2 * c) * a := by
          simp only [pow_two, mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    apply sq_eq_zero_iff.mp
    calc
      (a * c) ^ 2 = (a * c * a) * c := by simp only [pow_two, mul_assoc]
      _ = 0 := by rw [haca, zero_mul]
  constructor
  · intro h
    have descend : ∀ n : ℕ, a ^ (n + 1) * b = 0 → a * b = 0 := by
      intro n
      induction n with
      | zero =>
          intro h
          simpa using h
      | succ n ih =>
          intro h
          apply ih
          have h' : a ^ 2 * (a ^ n * b) = 0 := by
            rw [pow_two]
            simpa only [pow_succ', mul_assoc] using h
          simpa only [pow_succ', mul_assoc] using square_step (a ^ n * b) h'
    cases m with
    | zero => exact (hm rfl).elim
    | succ n => exact descend n h
  · intro h
    exact pow_mul_eq_zero_of_le (m := 1) (Nat.pos_of_ne_zero hm)
      (by simpa only [pow_one] using h)

/-- A positive power has the same left annihilators as the element itself in a
reduced monoid with zero. This is the opposite-monoid form of `pow_mul_eq_zero_iff`. -/
@[simp]
theorem mul_pow_eq_zero_iff {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} {m : ℕ} (hm : m ≠ 0) : a * b ^ m = 0 ↔ a * b = 0 := by
  simpa only [← MulOpposite.op_pow, ← MulOpposite.op_mul, MulOpposite.op_eq_zero_iff] using
    (pow_mul_eq_zero_iff (a := MulOpposite.op b) (b := MulOpposite.op a) hm)
