/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups

/-!
# No small subgroups from submonoid neighborhoods

A neighborhood of the identity containing only the trivial submonoid also
contains only the trivial subgroup. No compatibility between the group
operations and the topology is required.
-/

@[expose] public section

open scoped Topology

universe u

/-- A neighborhood containing only the trivial submonoid implies no small subgroups. -/
theorem NoSmallSubgroups.of_submonoid_neighborhood {N : Type u} [Group N] [TopologicalSpace N]
    (h : ∃ U ∈ 𝓝 (1 : N), ∀ M : Submonoid N, (M : Set N) ⊆ U → M = ⊥) :
    NoSmallSubgroups N := by
  rcases h with ⟨U, hU, h⟩
  refine ⟨⟨U, hU, fun H hH => ?_⟩⟩
  exact Subgroup.toSubmonoid_injective (h H.toSubmonoid hH)
