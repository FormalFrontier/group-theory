/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.SubgroupFamily
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Basic

/-!
# Boundary cases for subgroup-family topologies

The empty family on the original additive group of integers gives the indiscrete
uniformity and topology. A nonempty family consisting of the zero subgroup gives
the discrete topology and a proper zero neighborhood. Each check passes the original
whole group record to the basis and its original additive-group parent to the stock
right uniformity. No data instance is replaced.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- With no subgroups prescribed, the associated uniformity and topology are indiscrete.
The equalities also record the original whole group, its parents, the family, and the
exact topology parent of the stock right uniform space. -/
private theorem empty_family_indiscrete :
    let g : AddCommGroup ℤ := inferInstance
    let a : AddGroup ℤ := g.toAddGroup
    let m : AddMonoid ℤ := a.toAddMonoid
    let c : AddCommMonoid ℤ := g.toAddCommMonoid
    let H : Empty → @AddSubgroup ℤ a := Empty.elim
    let S : Empty → @AddSubmonoid ℤ m.toAddZeroClass := fun i => (H i).toAddSubmonoid
    let T : Empty → @AddSubsemigroup ℤ m.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis ℤ a := @AddSubgroup.familyBasis ℤ Empty g H
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ a B.topology
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ a B)
    g = (inferInstance : AddCommGroup ℤ) ∧
      a = g.toAddGroup ∧ m = a.toAddMonoid ∧ c = g.toAddCommMonoid ∧
      H = (Empty.elim : Empty → @AddSubgroup ℤ a) ∧
      S = (fun i => (H i).toAddSubmonoid) ∧
      T = (fun i => (H i).toAddSubmonoid.toAddSubsemigroup) ∧
      u.toTopologicalSpace = B.topology ∧ u.uniformity = ⊤ ∧ B.topology = ⊤ := by
  intro g a m c H S T B u
  have hn : @nhds ℤ B.topology 0 = ⊤ := by
    simpa using (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Empty g H)
  have hu : u.uniformity = ⊤ := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ B.topology 0) = ⊤
    rw [hn, Filter.comap_top]
  have he : u = ⊤ := UniformSpace.ext hu
  have ht : B.topology = ⊤ := congrArg (@UniformSpace.toTopologicalSpace ℤ) he
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, ht⟩

/-- The zero subgroup in a nonempty family makes the topology discrete. In contrast to
an empty family, it supplies a zero neighborhood that does not contain `1`. -/
private theorem zero_subgroup_discrete :
    let g : AddCommGroup ℤ := inferInstance
    let a : AddGroup ℤ := g.toAddGroup
    let m : AddMonoid ℤ := a.toAddMonoid
    let c : AddCommMonoid ℤ := g.toAddCommMonoid
    let H : Unit → @AddSubgroup ℤ a := fun _ => ⊥
    let S : Unit → @AddSubmonoid ℤ m.toAddZeroClass := fun i => (H i).toAddSubmonoid
    let T : Unit → @AddSubsemigroup ℤ m.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis ℤ a := @AddSubgroup.familyBasis ℤ Unit g H
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ a B.topology
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ a B)
    g = (inferInstance : AddCommGroup ℤ) ∧
      a = g.toAddGroup ∧ m = a.toAddMonoid ∧ c = g.toAddCommMonoid ∧
      H = (fun _ : Unit => (⊥ : @AddSubgroup ℤ a)) ∧
      S = (fun i => (H i).toAddSubmonoid) ∧
      T = (fun i => (H i).toAddSubmonoid.toAddSubsemigroup) ∧
      u.toTopologicalSpace = B.topology ∧
      u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) ∧ B.topology = ⊥ ∧
      ({0} : Set ℤ) ∈ @nhds ℤ B.topology 0 ∧ (1 : ℤ) ∉ ({0} : Set ℤ) := by
  intro g a m c H S T B u
  have hn : @nhds ℤ B.topology 0 = 𝓟 ({0} : Set ℤ) := by
    simpa [H] using (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Unit g H)
  have hu : u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ B.topology 0) = _
    rw [hn, Filter.comap_principal]
    congr 1
    ext p
    simp [SetRel.id, add_neg_eq_zero, eq_comm]
  have he : u = ⊥ := UniformSpace.ext hu
  have ht : B.topology = ⊥ := congrArg (@UniformSpace.toTopologicalSpace ℤ) he
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, ht, ?_, ?_⟩
  · rw [hn]
    exact Filter.mem_principal_self _
  · simp
