/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Tactic

/-!
# Nilpotency classes under semiconjugacy, powers and maps

A diagonal semiconjugacy `SemiconjBy a x a` turns the vanishing of a power of `x`
into the vanishing of the next power of `a`. Consequently, the nilpotency class of
`a` is at most one more than that of `x`, provided `x` is nilpotent.

The class of `a ^ n` is `(nilpotencyClass a + n - 1) / n` for every natural
exponent `n`. For positive exponents this is the round-up quotient; at exponent
zero the formula uses total natural-number division, not a ceiling at zero.
Unital monoid maps that preserve and reflect zero preserve the nilpotency class.
Zero reflection, rather than injectivity, is sufficient.

This module uses Mathlib's semiconjugacy and nilpotency-class APIs.
-/

@[expose] public section

universe u v w

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

/-- The nilpotency class of a power, using total natural-number division. -/
theorem nilpotencyClass_pow
    {M : Type u} [MonoidWithZero M] (a : M) (n : ℕ) :
    nilpotencyClass (a ^ n) = (nilpotencyClass a + n - 1) / n := by
  classical
  rcases subsingleton_or_nontrivial M with hM | hM
  · let : Subsingleton M := hM
    simp only [nilpotencyClass_eq_zero_of_subsingleton, zero_add]
    by_cases hn : n = 0
    · simp [hn]
    · exact (Nat.div_eq_of_lt (by omega : n - 1 < n)).symm
  · let : Nontrivial M := hM
    by_cases hn : n = 0
    · subst n
      have hone : nilpotencyClass (1 : M) = 0 := by
        by_contra h
        have hnil : IsNilpotent (1 : M) :=
          isNilpotent_of_pos_nilpotencyClass (Nat.pos_of_ne_zero h)
        have hz : (1 : M) = 0 := by
          simpa only [one_pow] using pow_nilpotencyClass hnil
        exact one_ne_zero hz
      simpa only [pow_zero, Nat.div_zero] using hone
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_cases ha : IsNilpotent a
    · let c := nilpotencyClass a
      let k := (c + n - 1) / n
      have hc : 0 < c := (pos_nilpotencyClass_iff (x := a)).2 ha
      have hdiv : (c + n - 1) % n + n * k = c + n - 1 :=
        Nat.mod_add_div (c + n - 1) n
      have hmod : (c + n - 1) % n < n := Nat.mod_lt _ hnpos
      have hk : 0 < k := by
        by_contra hk
        have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
        rw [hk0, Nat.mul_zero, Nat.add_zero] at hdiv
        omega
      have hkpred : k - 1 + 1 = k := by omega
      have hprod : n * (k - 1) + n = n * k := by
        calc
          n * (k - 1) + n = n * (k - 1 + 1) := by
            simp only [Nat.mul_add, Nat.mul_one]
          _ = n * k := by rw [hkpred]
      have hupper : c ≤ n * k := by omega
      have hlower : n * (k - 1) ≤ c - 1 := by omega
      -- At exponent k the power vanishes; at exponent k - 1 it cannot vanish.
      have hzero : (a ^ n) ^ (k - 1 + 1) = 0 := by
        rw [hkpred, ← pow_mul]
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hupper
        rw [hr, pow_add, show a ^ c = 0 from pow_nilpotencyClass ha, zero_mul]
      have hnonzero : (a ^ n) ^ (k - 1) ≠ 0 := by
        intro hz
        apply pow_pred_nilpotencyClass ha
        change a ^ (c - 1) = 0
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hlower
        rw [hr, pow_add, pow_mul, hz, zero_mul]
      have hindex : nilpotencyClass (a ^ n) = k - 1 + 1 :=
        (nilpotencyClass_eq_succ_iff (x := a ^ n) (k := k - 1)).2
          ⟨hzero, hnonzero⟩
      exact hindex.trans hkpred
    · have hclass : nilpotencyClass a = 0 := by
        by_contra h
        exact ha (isNilpotent_of_pos_nilpotencyClass (Nat.pos_of_ne_zero h))
      have hpowclass : nilpotencyClass (a ^ n) = 0 := by
        by_contra h
        exact ha (IsNilpotent.of_pow
          (isNilpotent_of_pos_nilpotencyClass (Nat.pos_of_ne_zero h)))
      rw [hpowclass, hclass, zero_add]
      exact (Nat.div_eq_of_lt (by omega : n - 1 < n)).symm

/-- A unital monoid map with trivial zero fibre preserves the nilpotency class. -/
theorem nilpotencyClass_map
    {M : Type u} {N : Type v} {F : Type w}
    [MonoidWithZero M] [MonoidWithZero N]
    [FunLike F M N] [MonoidWithZeroHomClass F M N]
    (f : F) (hf : ∀ a : M, f a = 0 → a = 0) (a : M) :
    nilpotencyClass (f a) = nilpotencyClass a := by
  have hpow (n : ℕ) : (f a) ^ n = 0 ↔ a ^ n = 0 := by
    constructor
    · intro h
      apply hf (a ^ n)
      simpa only [map_pow] using h
    · intro h
      simpa only [map_pow, map_zero] using congrArg f h
  have hsucc (k : ℕ) :
      nilpotencyClass (f a) = k + 1 ↔ nilpotencyClass a = k + 1 := by
    simp only [nilpotencyClass_eq_succ_iff, ne_eq, hpow]
  cases ha : nilpotencyClass a with
  | zero =>
      cases hfa : nilpotencyClass (f a) with
      | zero => rfl
      | succ k =>
          have h := (hsucc k).mp hfa
          simp [ha] at h
  | succ k =>
      exact (hsucc k).mpr ha
