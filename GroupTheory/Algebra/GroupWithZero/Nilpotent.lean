/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Semiconj.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
public import GroupTheory.Algebra.Divisibility.Basic
import Mathlib.Tactic

/-!
# Nilpotency class bounds and transport

A diagonal semiconjugacy `SemiconjBy a x a` turns the vanishing of a power of `x`
into the vanishing of the next power of `a`. Consequently, the nilpotency class of
`a` is at most one more than that of `x`, provided `x` is nilpotent.

The class of `a ^ n` is `(nilpotencyClass a + n - 1) / n` for every natural
exponent `n`. For positive exponents this is the round-up quotient; at exponent
zero the formula uses total natural-number division, not a ceiling at zero.
Unital monoid maps that preserve and reflect zero preserve the nilpotency class.
Zero reflection, rather than injectivity, is sufficient.

A nilpotent element bounds the nilpotency class of any commuting multiple of it.
In particular, multiplication by a commuting element does not increase its class.

This module uses Mathlib's semiconjugacy and nilpotency-class APIs.

* `SemiconjBy.nilpotencyClass_mul_le_add_one`: a bound for a factored target.
* `nilpotencyClass_mul_le_add_one`: the total cyclic-product bound.
-/

@[expose] public section

universe u v w

namespace SemiconjBy

/-- Transfer nilpotence and its bound along an intertwining relation. -/
private theorem nilpotencyClass_mul_aux {M : Type u} [MonoidWithZero M] {a b x : M}
    (h : SemiconjBy a x (a * b)) (hx : IsNilpotent x) :
    IsNilpotent (a * b) ∧ nilpotencyClass (a * b) ≤ nilpotencyClass x + 1 := by
  have hp := h.pow_right (nilpotencyClass x)
  change a * x ^ nilpotencyClass x = (a * b) ^ nilpotencyClass x * a at hp
  have hz : (a * b) ^ (nilpotencyClass x + 1) = 0 := by
    calc
      (a * b) ^ (nilpotencyClass x + 1) =
          (a * b) ^ nilpotencyClass x * a * b := by
            rw [pow_succ, mul_assoc]
      _ = a * x ^ nilpotencyClass x * b := by rw [← hp]
      _ = 0 := by rw [pow_nilpotencyClass hx, mul_zero, zero_mul]
  refine ⟨IsNilpotent.mk _ _ hz, ?_⟩
  by_contra hb
  cases hc : nilpotencyClass (a * b) with
  | zero => omega
  | succ k =>
    have hk : (a * b) ^ k ≠ 0 :=
      (nilpotencyClass_eq_succ_iff.mp hc).2
    exact hk (pow_eq_zero_of_le (by omega) hz)

/-- An intertwining relation bounds the nilpotency class of a product. -/
theorem nilpotencyClass_mul_le_add_one {M : Type u} [MonoidWithZero M] {a b x : M}
    (h : SemiconjBy a x (a * b)) (hx : IsNilpotent x) :
    nilpotencyClass (a * b) ≤ nilpotencyClass x + 1 :=
  (nilpotencyClass_mul_aux h hx).2


/-- Diagonal semiconjugacy bounds nilpotency class by one more than that of the other element. -/
theorem nilpotencyClass_le_add_one {M : Type u} [MonoidWithZero M] {a x : M}
    (h : SemiconjBy a x a) (hx : IsNilpotent x) :
    nilpotencyClass a ≤ nilpotencyClass x + 1 := by
  have h' : SemiconjBy a x (a * (1 : M)) := by
    simpa only [mul_one] using h
  simpa only [mul_one] using nilpotencyClass_mul_le_add_one h' hx


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

namespace Commute

/-- A commuting multiple of a nilpotent element has no larger nilpotency class. -/
public theorem nilpotencyClass_le_of_dvd
    {M : Type u} [MonoidWithZero M] {a c : M}
    (hcomm : Commute a c) (hdvd : a ∣ c) (hnil : IsNilpotent a) :
    nilpotencyClass c ≤ nilpotencyClass a := by
  have hkill : c ^ nilpotencyClass a = 0 := by
    obtain ⟨d, hd⟩ := hcomm.pow_dvd_pow_of_dvd hdvd (nilpotencyClass a)
    simpa only [pow_nilpotencyClass hnil, zero_mul] using hd
  cases hc : nilpotencyClass c with
  | zero => exact Nat.zero_le _
  | succ k =>
    have hpred : c ^ k ≠ 0 :=
      ((nilpotencyClass_eq_succ_iff (x := c) (k := k)).mp hc).2
    by_contra hle
    have hk : nilpotencyClass a ≤ k := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
    apply hpred
    rw [hr, pow_add, hkill, zero_mul]

/-- Multiplication by a commuting element does not increase a nilpotent element's class. -/
public theorem nilpotencyClass_mul_le_left
    {M : Type u} [MonoidWithZero M] {a b : M}
    (hcomm : Commute a b) (hnil : IsNilpotent a) :
    nilpotencyClass (a * b) ≤ nilpotencyClass a := by
  exact ((Commute.refl a).mul_right hcomm).nilpotencyClass_le_of_dvd ⟨b, rfl⟩ hnil

end Commute

/-- The nilpotency class of a cyclic product is bounded by that of its swap plus one. -/
theorem nilpotencyClass_mul_le_add_one {M : Type u} [MonoidWithZero M] (a b : M) :
    nilpotencyClass (a * b) ≤ nilpotencyClass (b * a) + 1 := by
  by_cases h : IsNilpotent (b * a)
  · exact SemiconjBy.nilpotencyClass_mul_le_add_one
      (show SemiconjBy a (b * a) (a * b) from (mul_assoc a b a).symm) h
  · have hn : ¬ IsNilpotent (a * b) := by
      intro hab
      apply h
      exact (SemiconjBy.nilpotencyClass_mul_aux
        (show SemiconjBy b (a * b) (b * a) from (mul_assoc b a b).symm) hab).1
    have hz : nilpotencyClass (a * b) = 0 := by
      by_contra hne
      exact hn (isNilpotent_of_pos_nilpotencyClass (by omega))
    rw [hz]
    exact Nat.zero_le _

example {M : Type u} [MonoidWithZero M] (a b : M) :
    nilpotencyClass (a * b) ≤ nilpotencyClass (b * a) + 1 ∧
      nilpotencyClass (b * a) ≤ nilpotencyClass (a * b) + 1 :=
  ⟨nilpotencyClass_mul_le_add_one a b, nilpotencyClass_mul_le_add_one b a⟩
