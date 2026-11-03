/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# No small subgroups in nonarchimedean groups

A nonarchimedean group has no small subgroups exactly when its given topology is discrete.
An open subgroup contained in a no-small-subgroups neighborhood must be trivial, so the
identity singleton is open. The topological-group discrete criterion then applies.

The forward implication is an explicit theorem, not an instance, to keep instance search
independent of the discrete-to-no-small-subgroups constructor.

## References

* Mathlib's `Topology.Algebra.Nonarchimedean.Basic`, `Topology.Algebra.OpenSubgroup`, and
  `Topology.Algebra.Group.Basic`, for the open-subgroup basis and singleton discrete criterion.
-/

@[expose] public section

open scoped Topology

universe u

/-- A nonarchimedean group with no small subgroups is discrete. -/
theorem NoSmallSubgroups.discreteTopology_of_nonarchimedean
    {G : Type u} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [NoSmallSubgroups G] : DiscreteTopology G := by
  obtain ⟨U, hU, hsub⟩ := NoSmallSubgroups.exists_nhds_one_subgroup_eq_bot (G := G)
  obtain ⟨V, hVU⟩ := NonarchimedeanGroup.is_nonarchimedean U hU
  have hVbot : V.toSubgroup = ⊥ := hsub V.toSubgroup hVU
  have hVopen : IsOpen (V.toSubgroup : Set G) := V.isOpen
  apply discreteTopology_of_isOpen_singleton_one
  simpa only [hVbot, Subgroup.coe_bot] using hVopen

/-- A nonarchimedean group has no small subgroups exactly when it is discrete. -/
theorem noSmallSubgroups_iff_discreteTopology_of_nonarchimedean
    {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G] :
    NoSmallSubgroups G ↔ DiscreteTopology G := by
  constructor
  · intro h
    have : NoSmallSubgroups G := h
    exact NoSmallSubgroups.discreteTopology_of_nonarchimedean
  · intro h
    have : DiscreteTopology G := h
    infer_instance
