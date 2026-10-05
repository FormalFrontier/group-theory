/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.ConnectedComponentQuotient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Basic

/-!
# Boundary cases for identity-component quotients

The connected real additive group (written multiplicatively) has trivial
identity-component quotient. A discrete two-element group has trivial
identity component but nontrivial quotient. An indiscrete, non-Hausdorff group
has a Hausdorff singleton quotient. Their product gives a group for which the
identity component and its totally disconnected quotient are both nontrivial.
-/

section

namespace GroupTheoryTest.Topology.ConnectedComponentQuotient

/-- The additive real group, in multiplicative notation. -/
public abbrev RealGroup := Multiplicative ℝ

private instance : PreconnectedSpace RealGroup :=
  inferInstanceAs (PreconnectedSpace ℝ)

/-- The additive two-element group, in multiplicative notation. -/
public abbrev TwoGroup := Multiplicative (ZMod 2)

private instance : TopologicalSpace TwoGroup := ⊥

private instance : DiscreteTopology TwoGroup := ⟨rfl⟩

/-- The additive three-element group with the indiscrete topology, in
multiplicative notation. -/
public abbrev IndiscreteGroup := Multiplicative (ZMod 3)

private instance : TopologicalSpace IndiscreteGroup := ⊤

/-- Product of a connected group and a nontrivial discrete group. -/
public abbrev MixedGroup := RealGroup × TwoGroup

/-- A connected group has no nontrivial quotient by its identity component. -/
theorem real_component_eq_top : Subgroup.connectedComponentOfOne RealGroup = ⊤ := by
  ext element
  change element ∈ connectedComponent (1 : RealGroup) ↔ True
  simp

/-- The connected real group's quotient has just one element. -/
theorem real_quotient_subsingleton :
    Subsingleton (QuotientGroup.connectedComponentQuotient RealGroup) :=
  QuotientGroup.subsingleton_iff.mpr real_component_eq_top

/-- The component of a nontrivial discrete group consists only of its identity. -/
theorem discrete_component_eq_bot : Subgroup.connectedComponentOfOne TwoGroup = ⊥ := by
  ext element
  change element ∈ connectedComponent (1 : TwoGroup) ↔ element = 1
  simp

/-- A nontrivial discrete group remains nontrivial after taking this quotient. -/
theorem discrete_quotient_nontrivial :
    Nontrivial (QuotientGroup.connectedComponentQuotient TwoGroup) :=
  QuotientGroup.nontrivial_iff.mpr (by rw [discrete_component_eq_bot]; exact bot_ne_top)

/-- The indiscrete group is not Hausdorff, although its identity-component
quotient is Hausdorff. -/
theorem indiscrete_not_hausdorff : ¬ T2Space IndiscreteGroup := by
  intro hT2
  have hclosed : IsClosed ({1} : Set IndiscreteGroup) :=
    (@T2Space.t1Space IndiscreteGroup _ hT2).t1 1
  rcases (IndiscreteTopology.isClosed_iff _).mp hclosed with hempty | huniv
  · exact Set.singleton_ne_empty _ hempty
  · have hsub : Subsingleton IndiscreteGroup := by
      constructor
      intro first second
      have hx : first = 1 := Set.mem_singleton_iff.mp (huniv.symm ▸ Set.mem_univ first)
      have hy : second = 1 := Set.mem_singleton_iff.mp (huniv.symm ▸ Set.mem_univ second)
      exact hx.trans hy.symm
    exact not_subsingleton IndiscreteGroup hsub

/-- An indiscrete group has a one-element identity-component quotient. -/
theorem indiscrete_quotient_subsingleton :
    Subsingleton (QuotientGroup.connectedComponentQuotient IndiscreteGroup) := by
  apply QuotientGroup.subsingleton_iff.mpr
  ext element
  change element ∈ connectedComponent (1 : IndiscreteGroup) ↔ True
  simp

/-- The closed-normal quotient is Hausdorff even though its source is not. -/
theorem indiscrete_quotient_hausdorff :
    T2Space (QuotientGroup.connectedComponentQuotient IndiscreteGroup) := inferInstance

/-- The mixed group's identity component contains a nonidentity real element. -/
theorem mixed_component_nontrivial :
    Nontrivial (Subgroup.connectedComponentOfOne MixedGroup) := by
  have hmem : ((Multiplicative.ofAdd (1 : ℝ)), (1 : TwoGroup)) ∈
      Subgroup.connectedComponentOfOne MixedGroup := by
    change _ ∈ connectedComponent (1 : MixedGroup)
    rw [show (1 : MixedGroup) = ((1 : RealGroup), (1 : TwoGroup)) from rfl,
      connectedComponent_prod]
    exact ⟨by simp, mem_connectedComponent⟩
  let element : Subgroup.connectedComponentOfOne MixedGroup := ⟨_, hmem⟩
  have hx : element ≠ 1 := by
    intro heq
    have hre := congrArg (fun mixedElement : MixedGroup => Multiplicative.toAdd mixedElement.1)
      (congrArg Subtype.val heq)
    change (1 : ℝ) = 0 at hre
    norm_num at hre
  exact ⟨⟨element, 1, hx⟩⟩

/-- The quotient of the mixed group maps onto its discrete factor through the
universal continuous factorization. -/
theorem mixed_quotient_nontrivial :
    Nontrivial (QuotientGroup.connectedComponentQuotient MixedGroup) := by
  let projection : MixedGroup →ₜ* TwoGroup := ContinuousMonoidHom.snd RealGroup TwoGroup
  have hsurj : Function.Surjective (QuotientGroup.connectedComponentQuotientLift projection) := by
    intro targetElement
    refine ⟨QuotientGroup.connectedComponentQuotientMk MixedGroup (1, targetElement), ?_⟩
    simpa [projection] using
      QuotientGroup.connectedComponentQuotientLift_mk_apply projection (1, targetElement)
  exact hsurj.nontrivial

end GroupTheoryTest.Topology.ConnectedComponentQuotient

end
