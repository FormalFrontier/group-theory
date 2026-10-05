/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.ConnectedComponentOpenSubgroup
public import GroupTheoryTest.Topology.ConnectedComponentQuotient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Constructions.SumProd

/-!
# Open-subgroup separation and identity-component images in familiar groups

The connected additive real group has no proper open subgroups; the infinite
discrete integer group has an open subgroup missing a specified nonidentity
point. The noninjective projection from their product onto the real factor
is an open surjection and maps the identity component densely onto its target.
The finite indiscrete group shows that the subgroup statement needs no
Hausdorff hypothesis.
-/

@[expose] public section

open scoped Topology

namespace GroupTheoryTest.Topology.ConnectedComponentOpenSubgroup

open GroupTheoryTest.Topology.ConnectedComponentQuotient (IndiscreteGroup)

public abbrev RealGroup := Multiplicative ℝ
public abbrev IntegerGroup := Multiplicative ℤ

private instance : PreconnectedSpace RealGroup :=
  inferInstanceAs (PreconnectedSpace ℝ)

private instance : TopologicalSpace IntegerGroup := ⊥
private instance : DiscreteTopology IntegerGroup := ⟨rfl⟩

private instance : LocallyCompactSpace IntegerGroup :=
  isCompact_singleton.locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_discrete {1}).mem_nhds (Set.mem_singleton (1 : IntegerGroup)))

private theorem real_component_eq_top : Subgroup.connectedComponentOfOne RealGroup = ⊤ := by
  ext element
  change element ∈ connectedComponent (1 : RealGroup) ↔ True
  simp

/-- The connected real group has no proper open subgroup. -/
theorem real_openSubgroup_eq_top (H : OpenSubgroup RealGroup) :
    (H : Subgroup RealGroup) = ⊤ := by
  apply eq_top_iff.mpr
  have hle : Subgroup.connectedComponentOfOne RealGroup ≤ (H : Subgroup RealGroup) := by
    rw [Subgroup.connectedComponentOfOne_eq_iInf_openSubgroup]
    exact iInf_le _ H
  simpa only [real_component_eq_top] using hle

private theorem integer_component_eq_bot :
    Subgroup.connectedComponentOfOne IntegerGroup = ⊥ := by
  ext element
  change element ∈ connectedComponent (1 : IntegerGroup) ↔ element = 1
  simp

/-- A nonidentity integer is excluded by a proper open subgroup. -/
theorem integer_exists_proper_openSubgroup :
    ∃ H : OpenSubgroup IntegerGroup,
      Multiplicative.ofAdd (1 : ℤ) ∉ H ∧ H ≠ ⊤ := by
  have hnot : Multiplicative.ofAdd (1 : ℤ) ∉
      Subgroup.connectedComponentOfOne IntegerGroup := by
    rw [integer_component_eq_bot]
    change Multiplicative.ofAdd (1 : ℤ) ≠ 1
    norm_num
  obtain ⟨H, hmissing⟩ :=
    Subgroup.exists_openSubgroup_not_mem_of_not_mem_connectedComponentOfOne hnot
  refine ⟨H, hmissing, ?_⟩
  intro htop
  apply hmissing
  rw [htop]
  exact OpenSubgroup.mem_top _

local instance : TopologicalSpace IndiscreteGroup := ⊤

local instance : LocallyCompactSpace IndiscreteGroup :=
  isCompact_univ.locallyCompactSpace_of_mem_nhds_of_group (x := (1 : IndiscreteGroup))
    Filter.univ_mem

/-- All open subgroups of a non-Hausdorff finite indiscrete group are the whole group. -/
theorem indiscrete_openSubgroup_eq_top_and_not_hausdorff (H : OpenSubgroup IndiscreteGroup) :
    (H : Subgroup IndiscreteGroup) = ⊤ ∧ ¬ T2Space IndiscreteGroup := by
  constructor
  · apply eq_top_iff.mpr
    have hle : Subgroup.connectedComponentOfOne IndiscreteGroup ≤
        (H : Subgroup IndiscreteGroup) := by
      rw [Subgroup.connectedComponentOfOne_eq_iInf_openSubgroup]
      exact iInf_le _ H
    have htop : Subgroup.connectedComponentOfOne IndiscreteGroup = ⊤ := by
      ext element
      change element ∈ connectedComponent (1 : IndiscreteGroup) ↔ True
      simp
    simpa only [htop] using hle
  · intro hT2
    have hT0 : T0Space IndiscreteGroup :=
      @T1Space.t0Space IndiscreteGroup _ (@T2Space.t1Space IndiscreteGroup _ hT2)
    have hsub : Subsingleton IndiscreteGroup :=
      (@subsingleton_iff_indiscreteTopology IndiscreteGroup _ hT0).mpr inferInstance
    exact not_subsingleton IndiscreteGroup hsub

/-- The open product projection has a nontrivial kernel. -/
theorem projection_not_injective :
    ¬ Function.Injective (ContinuousMonoidHom.fst RealGroup IntegerGroup) := by
  intro hinjective
  have heq : ((1 : RealGroup), (1 : IntegerGroup)) =
      ((1 : RealGroup), Multiplicative.ofAdd (1 : ℤ)) :=
    hinjective rfl
  have hbad : (0 : ℤ) = 1 :=
    congrArg (fun pair : RealGroup × IntegerGroup => Multiplicative.toAdd pair.2) heq
  exact zero_ne_one hbad

/-- The identity-component image of an open noninjective projection is dense
in the whole connected real factor. -/
theorem closure_projection_component_eq_univ :
    closure ((ContinuousMonoidHom.fst RealGroup IntegerGroup) ''
      (Subgroup.connectedComponentOfOne (RealGroup × IntegerGroup) :
        Set (RealGroup × IntegerGroup))) = Set.univ := by
  calc
    closure ((ContinuousMonoidHom.fst RealGroup IntegerGroup) ''
        (Subgroup.connectedComponentOfOne (RealGroup × IntegerGroup) :
          Set (RealGroup × IntegerGroup))) =
        (Subgroup.connectedComponentOfOne RealGroup : Set RealGroup) :=
      ContinuousMonoidHom.closure_image_connectedComponentOfOne
        (ContinuousMonoidHom.fst RealGroup IntegerGroup)
          (isOpenQuotientMap_fst (Y := IntegerGroup))
    _ = Set.univ := by rw [real_component_eq_top]; rfl

end GroupTheoryTest.Topology.ConnectedComponentOpenSubgroup
