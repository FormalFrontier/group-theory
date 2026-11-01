/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.GroupWithZero.Reduced
public import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.GCD

/-!
# Equality of powers in reduced rings

Two elements of a reduced ring are equal if their powers agree at two coprime natural
exponents. More generally, equality at two natural exponents is equivalent to equality
at their gcd. The ring need not be commutative, and the elements need not be regular.
Zero exponents and the zero ring are included.

The coprime criterion uses Mathlib's natural-number modular-inverse API and the
positive-power annihilator criterion for reduced monoids with zero. The gcd criterion
then factors the two exponents by their gcd.

## Main results

* `IsReduced.eq_of_pow_eq_pow_of_coprime`: coprime powers distinguish elements.
* `IsReduced.pow_gcd_eq_pow_gcd_iff`: equality of two powers is detected at the gcd.
-/

@[expose] public section

universe u

/-- In a reduced ring, equality at two coprime natural powers implies equality.
No commutativity or regularity assumption on the elements is needed. -/
theorem IsReduced.eq_of_pow_eq_pow_of_coprime {R : Type u} [Ring R] [IsReduced R]
    {x y : R} {m n : Nat} (hcop : Nat.Coprime m n) (hm : x ^ m = y ^ m)
    (hn : x ^ n = y ^ n) : x = y := by
  by_cases hn0 : n = 0
  · subst n
    have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hcop
    simpa only [hm1, pow_one] using hm
  by_cases hn1 : n = 1
  · simpa only [hn1, pow_one] using hn
  have hgt : 1 < n := by
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ k =>
      cases k with
      | zero => exact (hn1 rfl).elim
      | succ k => exact Nat.succ_lt_succ (Nat.succ_pos k)
  obtain ⟨a, _, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hgt
  let b : Nat := m * a / n
  have hab : m * a = n * b + 1 := by
    calc
      m * a = m * a % n + n * (m * a / n) := (Nat.mod_add_div _ _).symm
      _ = n * b + 1 := by rw [ha, Nat.add_comm]
  -- Both sides use the same left factor; no factors from `x` and `y` are interchanged.
  have hxy : (x ^ n) ^ b * x = (x ^ n) ^ b * y := by
    calc
      (x ^ n) ^ b * x = x ^ (m * a) := by
        rw [hab, pow_add, pow_mul, pow_one]
      _ = y ^ (m * a) := by
        simpa only [pow_mul] using congrArg (fun z : R => z ^ a) hm
      _ = (x ^ n) ^ b * y := by
        rw [hab, pow_add, pow_mul, pow_one, hn]
  have hzero : (x ^ n) ^ b * (x - y) = 0 := by
    rw [mul_sub, hxy, sub_self]
  by_cases hb : b = 0
  · have hsub : x - y = 0 := by
      simpa only [hb, pow_zero, one_mul] using hzero
    exact sub_eq_zero.mp hsub
  have hxn : x ^ n * (x - y) = 0 :=
    (_root_.pow_mul_eq_zero_iff hb).mp hzero
  have hx : x * (x - y) = 0 :=
    (_root_.pow_mul_eq_zero_iff hn0).mp hxn
  have hyn : y ^ n * (x - y) = 0 := by
    simpa only [hn] using hxn
  have hy : y * (x - y) = 0 :=
    (_root_.pow_mul_eq_zero_iff hn0).mp hyn
  have hsq : (x - y) ^ 2 = 0 := by
    rw [pow_two, sub_mul, hx, hy, sub_self]
  exact sub_eq_zero.mp (_root_.sq_eq_zero_iff.mp hsq)

/-- In a reduced ring, powers agree at the gcd of two natural exponents if and only
if they agree at both exponents. This includes zero exponents and the zero ring. -/
theorem IsReduced.pow_gcd_eq_pow_gcd_iff {R : Type u} [Ring R] [IsReduced R]
    (x y : R) (m n : Nat) :
    x ^ Nat.gcd m n = y ^ Nat.gcd m n ↔ x ^ m = y ^ m ∧ x ^ n = y ^ n := by
  obtain ⟨a, b, hcop, hma, hnb⟩ := Nat.exists_coprime m n
  constructor
  · intro h
    constructor
    · rw [hma, Nat.mul_comm a (Nat.gcd m n)]
      simpa only [pow_mul] using congrArg (fun z : R => z ^ a) h
    · rw [hnb, Nat.mul_comm b (Nat.gcd m n)]
      simpa only [pow_mul] using congrArg (fun z : R => z ^ b) h
  · rintro ⟨hm, hn⟩
    apply IsReduced.eq_of_pow_eq_pow_of_coprime hcop
    · rw [hma, Nat.mul_comm a (Nat.gcd m n)] at hm
      simpa only [pow_mul] using hm
    · rw [hnb, Nat.mul_comm b (Nat.gcd m n)] at hn
      simpa only [pow_mul] using hn
