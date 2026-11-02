/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous maps into groups with no small subgroups

For a compact space `X` and a topological group `G` with no small subgroups,
the group `C(X, G)` has no small subgroups in its compact-open topology.
The proof uses the positive-powers criterion for `NoSmallSubgroups` together with
Mathlib's compact-open neighborhoods and pointwise powers of continuous maps.
-/

@[expose] public section

universe u v

namespace ContinuousMap

/-- Continuous maps from a compact space into a topological group with no small
subgroups form a group with no small subgroups in the compact-open topology. -/
instance instNoSmallSubgroups
    {X : Type u} {G : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NoSmallSubgroups G] : NoSmallSubgroups C(X, G) := by
  obtain ⟨U, hU, h1U, _, hpow⟩ :=
    NoSmallSubgroups.exists_open_nhds_one_pow (G := G)
  refine NoSmallSubgroups.of_nhds_one_pow
    (U := {f : C(X, G) | Set.MapsTo f Set.univ U}) ?_ ?_
  · apply (isOpen_setOfPred_mapsTo (X := X) isCompact_univ hU).mem_nhds
    intro x _
    change (1 : G) ∈ U
    exact h1U
  · intro f hf
    apply ContinuousMap.ext
    intro x
    change f x = 1
    apply hpow
    intro n hn
    simpa only [ContinuousMap.pow_apply] using hf n hn (Set.mem_univ x)

end ContinuousMap
