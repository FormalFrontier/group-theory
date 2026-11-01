/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Commute.Defs

/-!
# Powers of commuting divisible elements

Power divisibility in a monoid follows from divisibility and commutation of the divisor with
the dividend. `Commute.pow_dvd_pow_of_dvd` generalizes `pow_dvd_pow_of_dvd` from commutative
monoids to elementwise commutation.
-/

@[expose] public section

universe u

namespace Commute

/-- Powers of a divisor divide the corresponding powers of a commuting dividend. -/
public theorem pow_dvd_pow_of_dvd
    {M : Type u} [Monoid M] {a c : M}
    (hcomm : Commute a c) (hdvd : a ∣ c) (n : ℕ) :
    a ^ n ∣ c ^ n := by
  obtain ⟨d, hd⟩ := hdvd
  induction n with
  | zero =>
      simpa only [pow_zero] using (dvd_rfl : (1 : M) ∣ 1)
  | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨d * r, ?_⟩
      calc
        c ^ (n + 1) = c * c ^ n := pow_succ' c n
        _ = c * (a ^ n * r) := by rw [hr]
        _ = (c * a ^ n) * r := (mul_assoc c (a ^ n) r).symm
        _ = (a ^ n * c) * r :=
          congrArg (fun x : M => x * r) (hcomm.pow_left n).eq.symm
        _ = (a ^ n * (a * d)) * r := by rw [hd]
        _ = a ^ (n + 1) * (d * r) := by
          simp only [pow_succ, mul_assoc]

end Commute
