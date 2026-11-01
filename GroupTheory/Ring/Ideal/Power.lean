/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Ring.Power
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Power differences modulo radical ideals

Equality of two powers modulo a radical ideal is detected at the greatest common
divisor of their exponents.
-/

@[expose] public section

universe u

namespace Ideal.IsRadical

/-- Membership of both power differences in a radical ideal is detected at the gcd exponent. -/
public theorem pow_gcd_sub_pow_gcd_mem_iff
    {R : Type u} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    (x y : R) (m n : ℕ) :
    x ^ (Nat.gcd m n) - y ^ (Nat.gcd m n) ∈ I ↔
      (x ^ m - y ^ m ∈ I ∧ x ^ n - y ^ n ∈ I) := by
  let _ : IsReduced (R ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  simpa only [← (Ideal.Quotient.mk I).map_pow,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
    (IsReduced.pow_gcd_eq_pow_gcd_iff
      (Ideal.Quotient.mk I x) (Ideal.Quotient.mk I y) m n)

end Ideal.IsRadical
