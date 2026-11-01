/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Integrals of Pontryagin characters

A nontrivial continuous circle-valued character has integral zero against any
left-invariant measure. Applying this to the quotient of two distinct characters
gives their off-diagonal orthogonality. The domain need only be a monoid with
measurable translations; neither compactness nor finiteness of the measure is
required. The Bochner integral is zero by definition for nonintegrable functions.

The proof uses Mathlib's change-of-variables formula for the Bochner integral,
`MeasureTheory.map_mul_left_eq_self`, and the existing complex coercion of `Circle`.
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate

universe u

namespace PontryaginDual

variable {K : Type u} [Monoid K] [TopologicalSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K] [MeasurableMul K]
  (μ : Measure K) [Measure.IsMulLeftInvariant μ]

/-- The integral of a nontrivial Pontryagin character against a left-invariant
measure is zero. -/
theorem integral_eq_zero_of_ne_one (χ : PontryaginDual K) (hχ : χ ≠ 1) :
    (∫ x, (χ x : ℂ) ∂μ) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : K, χ g ≠ 1 :=
    not_forall.mp fun h => hχ (ext fun x => by simpa only [one_apply] using h x)
  have hm : StronglyMeasurable (fun x : K => (χ x : ℂ)) :=
    (continuous_subtype_val.comp (map_continuous χ)).stronglyMeasurable
  have htranslate : (∫ x, (χ (g * x) : ℂ) ∂μ) = ∫ x, (χ x : ℂ) ∂μ := by
    simpa only [map_mul_left_eq_self] using
      (integral_map_of_stronglyMeasurable (μ := μ) (measurable_const_mul g) hm).symm
  have hmul : (χ g : ℂ) * (∫ x, (χ x : ℂ) ∂μ) = ∫ x, (χ x : ℂ) ∂μ := by
    rw [← integral_const_mul]
    simpa only [_root_.map_mul, Circle.coe_mul] using htranslate
  have hzero : ((χ g : ℂ) - 1) * (∫ x, (χ x : ℂ) ∂μ) = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  have hgC : (χ g : ℂ) ≠ 1 := by
    intro h
    exact hg ((Circle.coe_eq_one (x := χ g)).mp h)
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hgC)

/-- Distinct Pontryagin characters are orthogonal under integration against any
left-invariant measure. -/
theorem integral_mul_conj_eq_zero (χ ψ : PontryaginDual K) (hχψ : χ ≠ ψ) :
    (∫ x, (χ x : ℂ) * conj (ψ x : ℂ) ∂μ) = 0 := by
  have hne : χ * ψ⁻¹ ≠ 1 := fun h => hχψ (mul_inv_eq_one.mp h)
  calc
    (∫ x, (χ x : ℂ) * conj (ψ x : ℂ) ∂μ) =
        ∫ x, ((χ * ψ⁻¹) x : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (χ x : ℂ) * conj (ψ x : ℂ) = ((χ * ψ⁻¹) x : ℂ)
        calc
          (χ x : ℂ) * conj (ψ x : ℂ) =
              (χ x : ℂ) * (((ψ x)⁻¹ : Circle) : ℂ) :=
            congrArg (fun z : ℂ => (χ x : ℂ) * z)
              (Circle.coe_inv_eq_conj (ψ x)).symm
          _ = ((χ x * (ψ x)⁻¹ : Circle) : ℂ) :=
            (Circle.coe_mul (χ x) ((ψ x)⁻¹)).symm
          _ = ((χ * ψ⁻¹) x : ℂ) := rfl
    _ = 0 := integral_eq_zero_of_ne_one μ (χ * ψ⁻¹) hne

end PontryaginDual
