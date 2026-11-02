/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.PontryaginDual
public import GroupTheory.Topology.PontryaginDual.Saturation
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Basic

/-!
# Surjectivity of evaluation for discrete groups

Every continuous circle-valued character of the compact-open Pontryagin dual of
a discrete group is evaluation at a group element. The group need not be
commutative: the evaluation characters separate points of the dual, and
saturation with respect to Haar measure makes their subgroup the whole bidual.

This is a surjectivity theorem, not an injectivity or reflexivity theorem for
noncommutative groups.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.11), for bidual evaluation in the classical abelian setting.
* Mathlib's `Topology.Algebra.PontryaginDual` supplies compactness of the dual of
  a discrete monoid, and `MeasureTheory.Measure.Haar.Basic` supplies Haar measure.
* `PontryaginDual.subgroup_eq_top_of_separatesPoints` supplies saturation of a
  point-separating subgroup of characters.
-/

@[expose] public section

universe u

/-- Canonical Pontryagin evaluation is surjective for every discrete group,
without a commutativity hypothesis on that group. -/
theorem PontryaginDual.eval_surjective_of_discrete
    (A : Type u) [Group A] [TopologicalSpace A] [DiscreteTopology A] :
    Function.Surjective (PontryaginDual.eval A) := by
  classical
  let : MeasurableSpace (PontryaginDual A) := borel (PontryaginDual A)
  let : BorelSpace (PontryaginDual A) := ⟨rfl⟩
  let μ : MeasureTheory.Measure (PontryaginDual A) :=
    MeasureTheory.Measure.haar (G := PontryaginDual A)
  let : MeasureTheory.Measure.IsHaarMeasure μ := inferInstance
  let : MeasureTheory.IsFiniteMeasure μ := inferInstance
  let : NeZero μ := inferInstance
  have h_range : (PontryaginDual.eval A).toMonoidHom.range = ⊤ := by
    apply PontryaginDual.subgroup_eq_top_of_separatesPoints μ
    intro χ ψ hχψ
    have h : ¬ ∀ a : A, χ a = ψ a := by
      intro h
      exact hχψ (PontryaginDual.ext h)
    obtain ⟨a, ha⟩ := not_forall.mp h
    refine ⟨PontryaginDual.eval A a, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    · simpa only [PontryaginDual.eval_apply] using ha
  change Function.Surjective (PontryaginDual.eval A).toMonoidHom
  exact MonoidHom.range_eq_top.mp h_range
