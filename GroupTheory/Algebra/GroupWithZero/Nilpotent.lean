/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic

/-!
# Nilpotency classes and semiconjugacy

A diagonal semiconjugacy `SemiconjBy a x a` turns the vanishing of a power of `x`
into the vanishing of the next power of `a`. Consequently, the nilpotency class of
`a` is at most one more than that of `x`, provided `x` is nilpotent.

This module uses Mathlib's semiconjugacy and nilpotency-class APIs.
-/

@[expose] public section

universe u

namespace SemiconjBy

/-- Diagonal semiconjugacy bounds nilpotency class by one more than that of the other element. -/
theorem nilpotencyClass_le_add_one {M : Type u} [MonoidWithZero M] {a x : M}
    (h : SemiconjBy a x a) (hx : IsNilpotent x) :
    nilpotencyClass a ≤ nilpotencyClass x + 1 := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · let : Subsingleton M := hM
    simp only [nilpotencyClass_eq_zero_of_subsingleton, Nat.zero_le]
  · let : Nontrivial M := hM
    have hpow : a * x ^ nilpotencyClass x = a ^ nilpotencyClass x * a :=
      h.pow_right (nilpotencyClass x)
    have ha_pow : a ^ (nilpotencyClass x + 1) = 0 := by
      calc
        a ^ (nilpotencyClass x + 1) = a ^ nilpotencyClass x * a := pow_succ a _
        _ = a * x ^ nilpotencyClass x := hpow.symm
        _ = 0 := by rw [pow_nilpotencyClass hx, mul_zero]
    by_contra hle
    have ha : IsNilpotent a :=
      isNilpotent_of_pos_nilpotencyClass (by omega)
    -- The predecessor power would inherit vanishing from the smaller exponent.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, nilpotencyClass a - 1 = nilpotencyClass x + 1 + k := by
      refine ⟨nilpotencyClass a - 1 - (nilpotencyClass x + 1), ?_⟩
      omega
    apply pow_pred_nilpotencyClass ha
    rw [hk, pow_add, ha_pow, zero_mul]

end SemiconjBy
