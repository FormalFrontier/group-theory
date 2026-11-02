/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Uniform positive-power detection in normed rings

In a normed ring with norm-homogeneous canonical integer multiplication, an element
whose positive powers all stay within one fixed radius strictly below one of the
identity is the identity. The bound must be uniform in the exponent.

The proof applies a reverse triangle estimate to successive squares. Unless the
initial deviation vanishes, these deviations grow geometrically, contradicting the
uniform bound. Neither commutativity, completeness nor a normalized norm of one is
needed. Geometric growth and the norm and scalar-action API are supplied by Mathlib.

The canonical integer action of any real seminormed space is norm-homogeneous; the
instance below obtains this from Mathlib's real scalar norm formula and integer
norm-cast identity. It changes no scalar action or seminormed-group structure.
-/

@[expose] public section

open Filter

universe u v

/-- The canonical integer action on a real seminormed space is norm-homogeneous,
with the standard norm on the integers. -/
instance (priority := 100) NormedSpace.toNormSMulClass_int
    {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℝ E] : NormSMulClass ℤ E where
  norm_smul z e := by
    rw [norm_zsmul ℝ, Int.norm_cast_real]

namespace NormedRing

variable {A : Type u} [NormedRing A] [NormSMulClass ℤ A]

private theorem norm_sq_sub_one_lower_bound (x : A) :
    2 * ‖x - 1‖ - ‖x - 1‖ ^ 2 ≤ ‖x ^ 2 - 1‖ := by
  have hid : (2 : ℤ) • (x - 1) = (x ^ 2 - 1) - (x - 1) * (x - 1) := by
    rw [two_zsmul]
    noncomm_ring
  have htri : 2 * ‖x - 1‖ ≤ ‖x ^ 2 - 1‖ + ‖(x - 1) * (x - 1)‖ := by
    calc
      2 * ‖x - 1‖ = ‖(2 : ℤ) • (x - 1)‖ := by
        rw [norm_smul]
        norm_num [Int.norm_eq_abs]
      _ = ‖(x ^ 2 - 1) - (x - 1) * (x - 1)‖ := by rw [hid]
      _ ≤ ‖x ^ 2 - 1‖ + ‖(x - 1) * (x - 1)‖ := norm_sub_le _ _
  nlinarith [norm_mul_le (x - 1) (x - 1)]

/-- If all positive powers of an element of a normed ring have distance at most
one fixed `r < 1` from the identity, the element is the identity. The integer
homogeneity assumption concerns the ring's canonical additive integer action.

Successive squaring gives geometric growth with factor `2 - r` for a nonzero
deviation, contradicting the uniform bound. No completeness, commutativity,
nontriviality or norm-one assumption is required. -/
theorem eq_one_of_forall_norm_pow_sub_one_le (x : A) (r : ℝ) (hr : r < 1)
    (hpow : ∀ n : ℕ, 0 < n → ‖x ^ n - 1‖ ≤ r) : x = 1 := by
  let a : ℕ → ℝ := fun k => ‖x ^ (2 ^ k) - 1‖
  have ha (k : ℕ) : a k ≤ r :=
    hpow (2 ^ k) (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
  by_contra hx
  have hzero : 0 < a 0 := by
    simpa [a] using norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hstep (k : ℕ) : (2 - r) * a k ≤ a (k + 1) := by
    have hlower := norm_sq_sub_one_lower_bound (x ^ (2 ^ k))
    have hsq : (x ^ (2 ^ k)) ^ 2 = x ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, pow_succ]
    rw [hsq] at hlower
    change 2 * a k - (a k) ^ 2 ≤ a (k + 1) at hlower
    have hquad := mul_le_mul_of_nonneg_right (ha k) (show 0 ≤ a k from norm_nonneg _)
    nlinarith
  have hlim : Tendsto a atTop atTop :=
    tendsto_atTop_of_geom_le hzero (by linarith : 1 < 2 - r) hstep
  obtain ⟨k, hk⟩ := (hlim.eventually (eventually_gt_atTop r)).exists
  exact (not_lt_of_ge (ha k)) hk

end NormedRing
