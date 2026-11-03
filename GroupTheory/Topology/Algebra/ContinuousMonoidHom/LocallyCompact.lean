/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Units
public import GroupTheory.Topology.Algebra.Group.Units
public import GroupTheory.Topology.FreeGroup

/-!
# Locally compact homomorphism spaces into monoids

Continuous monoid homomorphisms from a finitely generated discrete group into a
locally compact topological monoid form a locally compact space when the target's
identity singleton is closed. No `T1Space` or `T2Space` assumption on the target is required.

The proof uses the canonical units of the target, the homeomorphism
`ContinuousMonoidHom.toHomUnitsHomeomorph`, and the group-target theorem
`ContinuousMonoidHom.locallyCompactSpace_of_fg`. The compact-open topology and
units constructions are those of Mathlib.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G]
  [DiscreteTopology G] [Group.FG G] [Monoid D] [TopologicalSpace D]
  [ContinuousMul D] [LocallyCompactSpace D]

/-- Homomorphisms from a finitely generated discrete group into a locally compact
topological monoid with closed identity form a locally compact space. -/
theorem locallyCompactSpace_of_fg_of_isClosed_one (hOne : IsClosed ({1} : Set D)) :
    LocallyCompactSpace (G →ₜ* D) := by
  let : LocallyCompactSpace G := ⟨fun x n hn =>
    ⟨{x}, by simp, by simpa using mem_of_mem_nhds hn, isCompact_singleton⟩⟩
  let : LocallyCompactSpace Dˣ := Units.locallyCompactSpace_of_isClosed_one hOne
  let : T2Space Dˣ := Units.t2Space_of_isClosed_one hOne
  let : LocallyCompactSpace (G →ₜ* Dˣ) :=
    locallyCompactSpace_of_fg (G := G) (D := Dˣ)
  exact (toHomUnitsHomeomorph (G := G) (D := D)).locallyCompactSpace_iff.mpr inferInstance

end ContinuousMonoidHom
