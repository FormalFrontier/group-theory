/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.IsAddUnit
public import GroupTheory.MonoidLocalization.GrothendieckGroup.Ring
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotence in the Grothendieck ring of a semiring

The canonical homomorphism to a semiring's additive group completion reflects
nilpotence on additive units. More precisely, if the image of `a` has vanishing
`n`th power and `a` is an additive unit, then `a ^ (n + 1) = 0`.

The proof uses the stable additive kernel, not injectivity of the completion map.
This allows application to noncancellative semirings: to reflect nilpotence of a
polynomial coefficient, it suffices to know that coefficient is an additive unit.
-/

@[expose] public section

universe u

namespace Algebra.GrothendieckAddGroup

variable {A : Type u} [Semiring A] {a : A}

/-- The kernel of the canonical ring homomorphism consists of additively absorbed
semiring elements. -/
theorem ofRingHom_eq_zero_iff : ofRingHom A a = 0 ↔ ∃ c : A, a + c = c := by
  have hz : ofRingHom A (0 : A) = 0 := map_zero (ofRingHom A)
  rw [← hz, ofRingHom_apply, ofRingHom_apply, of_eq_iff_exists]
  simp only [zero_add]

/-- A vanishing power in the completion gives an explicit power bound in the
semiring for an additive unit, including the case `n = 0`. -/
theorem pow_succ_eq_zero_of_ofRingHom_pow_eq_zero (ha : IsAddUnit a) {n : ℕ}
    (h : ofRingHom A a ^ n = 0) : a ^ (n + 1) = 0 := by
  rw [← map_pow] at h
  obtain ⟨c, hc⟩ := ofRingHom_eq_zero_iff.mp h
  exact ha.pow_succ_eq_zero_of_add_eq hc

/-- The canonical map to the Grothendieck ring reflects nilpotence on additive
units of an arbitrary semiring. The canonical generator is the simp normal form
of `ofRingHom A a`, so this ring-homomorphism formulation is used explicitly. -/
theorem isNilpotent_ofRingHom_iff (ha : IsAddUnit a) :
    IsNilpotent (ofRingHom A a) ↔ IsNilpotent a := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, pow_succ_eq_zero_of_ofRingHom_pow_eq_zero ha hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← map_pow, hn, map_zero]⟩

end Algebra.GrothendieckAddGroup
