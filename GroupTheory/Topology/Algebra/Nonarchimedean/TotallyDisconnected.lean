/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Connected

import GroupTheory.Topology.CompactOpenSubgroup

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Topology.Separation.Profinite

/-!
# Open subgroups of totally disconnected locally compact groups

Van Dantzig's theorem gives a basis of open subgroups at the identity of a totally disconnected
locally compact group. Here weak local compactness suffices: total disconnectedness and the
compatible right uniformity supply the separation properties needed to obtain local compactness.
All these properties concern the given topology.

After deriving local compactness on the given topology, the proof applies
`NonarchimedeanGroup.of_locallyCompactSpace`. This reuses the open-subgroup basis construction
for locally compact, totally disconnected groups.

## References

* Van Dantzig's theorem on open subgroups of totally disconnected locally compact groups.
* Mathlib's `Topology.Algebra.Group.Basic` and `Topology.UniformSpace.Separation`, for the
  compatible right uniformity and its separation properties.
-/

@[expose] public section

universe u

/-- A weakly locally compact, totally disconnected topological group is nonarchimedean.
This is van Dantzig's open-subgroup theorem. -/
theorem TotallyDisconnectedSpace.nonarchimedeanGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [WeaklyLocallyCompactSpace G] :
    NonarchimedeanGroup G := by
  -- The right uniformity extends the given topology, so its regularity applies to that topology.
  have : RegularSpace G := by
    let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    infer_instance
  have : T2Space G := inferInstance
  have : LocallyCompactSpace G := inferInstance
  exact NonarchimedeanGroup.of_locallyCompactSpace
