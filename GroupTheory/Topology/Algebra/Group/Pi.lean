/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact coordinate subgroups

A coordinate subgroup that fixes the identity on an arbitrary set of indices is compact
when the original fibers outside that set are compact. No continuity of the group operations
or separation of the given topologies is required. The proof uses Mathlib's Tychonoff theorem
and compactness of singletons.
-/

universe u v

/-- Functions equal to one on `s` form a compact subgroup
when every fiber outside `s` is compact. -/
public theorem Subgroup.isCompact_pi_bot {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] {s : Set ι}
    (h : ∀ i ∉ s, IsCompact (Set.univ : Set (G i))) :
    IsCompact (↑(Subgroup.pi s (⊥ : ∀ i, Subgroup (G i))) : Set (∀ i, G i)) := by
  classical
  have hc : ∀ i, IsCompact (if i ∈ s then {(1 : G i)} else Set.univ) := fun i => by
    split_ifs with hi
    · exact isCompact_singleton
    · exact h i hi
  convert isCompact_pi_infinite hc using 1
  ext x
  simp [Subgroup.mem_pi]
