/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.Nonarchimedean
public import GroupTheory.Topology.Algebra.Nonarchimedean.TotallyDisconnected

import Mathlib.Topology.Compactness.Compact

/-!
# No small subgroups in totally disconnected locally compact groups

A weakly locally compact, totally disconnected topological group has no small subgroups
exactly when its given topology is discrete. Van Dantzig's open-subgroup theorem supplies
the nonarchimedean property, reducing the assertion to the nonarchimedean criterion.

For compact totally disconnected topological groups, no small subgroups is equivalent to
finiteness of the carrier. In the reverse direction, total disconnectedness supplies T₁
separation: finiteness alone would not imply discreteness of an arbitrary topology.

## References

* Van Dantzig's theorem, as formalized by `TotallyDisconnectedSpace.nonarchimedeanGroup`.
* Mathlib's `Topology.Compactness.Compact` and `Topology.Separation.Basic`, for compact
  discrete finiteness and discreteness of finite T₁ spaces.
-/

@[expose] public section

universe u

/-- A weakly locally compact, totally disconnected topological group has no small subgroups
exactly when it is discrete. -/
theorem noSmallSubgroups_iff_discreteTopology
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [WeaklyLocallyCompactSpace G] :
    NoSmallSubgroups G ↔ DiscreteTopology G := by
  have : NonarchimedeanGroup G := TotallyDisconnectedSpace.nonarchimedeanGroup G
  exact noSmallSubgroups_iff_discreteTopology_of_nonarchimedean

/-- A compact, totally disconnected topological group has no small subgroups exactly when
its carrier is finite. -/
theorem noSmallSubgroups_iff_finite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [CompactSpace G] : NoSmallSubgroups G ↔ Finite G := by
  constructor
  · intro h
    have : DiscreteTopology G := (noSmallSubgroups_iff_discreteTopology (G := G)).mp h
    exact finite_of_compact_of_discrete
  · intro h
    have : Finite G := h
    have : T1Space G := inferInstance
    have : DiscreteTopology G := inferInstance
    infer_instance
