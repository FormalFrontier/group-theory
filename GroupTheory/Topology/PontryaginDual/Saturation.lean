/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.PontryaginDual.Integral
public import GroupTheory.Topology.PontryaginDual.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Saturation of uniformly spanning character sets

On a compact monoid carrying a finite nonzero left-invariant measure, a set of
continuous circle-valued characters with uniformly dense complex linear span
contains every character. Consequently, a point-separating subgroup of the
Pontryagin dual is the whole dual.

The proof integrates against a missing character. Orthogonality annihilates the
span, whereas uniform approximation of that character would give a nonzero
diagonal integral.

## References

* `PontryaginDual.integral_mul_conj_eq_zero` supplies character orthogonality.
* `PontryaginDual.topologicalClosure_span_eq_top_of_separatesPoints` supplies the
  scalar Stone–Weierstrass density bridge for the subgroup corollary.
* Mathlib's bounded-continuous-function integrability and Bochner integral norm
  estimate supply the uniform error bound.
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate

universe u

/-- A set of characters whose scalar complex span is uniformly dense contains
every character, provided the compact monoid carries a finite nonzero
left-invariant measure. -/
theorem PontryaginDual.eq_univ_of_topologicalClosure_span_eq_top
    {K : Type u} [Monoid K] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [MeasurableMul K]
    (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [NeZero μ] [MeasureTheory.Measure.IsMulLeftInvariant μ]
    (S : Set (PontryaginDual K))
    (hS : (Submodule.span ℂ
      {f : C(K, ℂ) | ∃ χ ∈ S, ∀ x, f x = (χ x : ℂ)}).topologicalClosure = ⊤) :
    S = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro γ
  by_contra hγ
  let V : Submodule ℂ C(K, ℂ) := Submodule.span ℂ
    {f : C(K, ℂ) | ∃ χ ∈ S, ∀ x, f x = (χ x : ℂ)}
  have hV : V.topologicalClosure = ⊤ := hS
  let p : C(K, ℂ) :=
    (ContinuousMap.subtypeVal (Metric.sphere (0 : ℂ) 1)).comp γ.toContinuousMap
  have hcontinuous_integrable (f : C(K, ℂ)) : Integrable (fun x => f x) μ := by
    exact BoundedContinuousFunction.integrable μ
      (ContinuousMap.equivBoundedOfCompact K ℂ f)
  have hweighted_integrable (f : C(K, ℂ)) :
      Integrable (fun x => f x * conj (γ x : ℂ)) μ := by
    change Integrable (fun x => (f * star p) x) μ
    exact hcontinuous_integrable (f * star p)
  have hvanish (f : C(K, ℂ)) (hf : f ∈ V) :
      (∫ x, f x * conj (γ x : ℂ) ∂μ) = 0 := by
    refine Submodule.span_induction (R := ℂ)
      (p := fun (f : C(K, ℂ)) _ =>
        (∫ x, f x * conj (γ x : ℂ) ∂μ) = 0) ?_ ?_ ?_ ?_ hf
    · rintro f ⟨χ, hχ, hfχ⟩
      have hχγ : χ ≠ γ := fun h => hγ (h ▸ hχ)
      simpa only [hfχ] using
        PontryaginDual.integral_mul_conj_eq_zero μ χ γ hχγ
    · simp
    · intro f g _ _ hf hg
      simp only [ContinuousMap.add_apply, add_mul]
      rw [integral_add (hweighted_integrable f) (hweighted_integrable g), hf, hg,
        add_zero]
    · intro c f _ hf
      simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, hf, mul_zero]
  have hclosure : p ∈ closure (V : Set C(K, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, hV]
    exact Submodule.mem_top
  obtain ⟨f, hf, hdist⟩ :=
    Metric.mem_closure_iff.mp hclosure (1 / 2) (by norm_num)
  have hnorm : ‖p - f‖ < (1 / 2 : ℝ) := by
    simpa only [dist_eq_norm] using hdist
  have hdiag : (∫ x, p x * conj (γ x : ℂ) ∂μ) =
      μ.real Set.univ • (1 : ℂ) := by
    calc
      _ = ∫ _ : K, (1 : ℂ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (γ x : ℂ) * conj (γ x : ℂ) = 1
          rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel,
            Circle.coe_one]
      _ = _ := integral_const _
  have herror : (∫ x, (p x - f x) * conj (γ x : ℂ) ∂μ) =
      μ.real Set.univ • (1 : ℂ) := by
    simp_rw [sub_mul]
    rw [integral_sub (hweighted_integrable p) (hweighted_integrable f),
      hdiag, hvanish f hf, sub_zero]
  have hbound : ‖∫ x, (p x - f x) * conj (γ x : ℂ) ∂μ‖ ≤
      ‖p - f‖ * μ.real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun x => by
      calc
        ‖(p x - f x) * conj (γ x : ℂ)‖ = ‖p x - f x‖ := by
          rw [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
        _ ≤ ‖p - f‖ := (p - f).norm_coe_le_norm x
  have hm : 0 < μ.real Set.univ := measureReal_univ_pos (μ := μ)
  rw [herror, norm_smul, Real.norm_eq_abs, abs_of_pos hm, norm_one, mul_one] at hbound
  have hsmall : ‖p - f‖ < 1 := lt_trans hnorm (by norm_num)
  have hlt : ‖p - f‖ * μ.real Set.univ < μ.real Set.univ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hsmall hm
  exact (not_lt_of_ge hbound) hlt

/-- A point-separating subgroup of characters of a compact monoid is the whole
dual if the monoid carries a finite nonzero left-invariant measure. -/
theorem PontryaginDual.subgroup_eq_top_of_separatesPoints
    {K : Type u} [Monoid K] [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [MeasurableMul K]
    (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [NeZero μ] [MeasureTheory.Measure.IsMulLeftInvariant μ]
    (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) :
    S = ⊤ := by
  have hset : (S : Set (PontryaginDual K)) = Set.univ :=
    PontryaginDual.eq_univ_of_topologicalClosure_span_eq_top μ
      (S : Set (PontryaginDual K))
      (PontryaginDual.topologicalClosure_span_eq_top_of_separatesPoints S hS)
  apply Subgroup.ext
  intro χ
  change χ ∈ (S : Set (PontryaginDual K)) ↔ χ ∈ (⊤ : Subgroup (PontryaginDual K))
  rw [hset]
  simp only [Set.mem_univ, Subgroup.mem_top]
