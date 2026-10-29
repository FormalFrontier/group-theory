/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Dense finite generation

A finite set whose algebraically generated subgroup is dense gives a dense finitely
generated subgroup, and conversely. No finite generation of the ambient abstract group
is asserted. This equivalence only needs a group equipped with a topology.

For topological groups, density of a subgroup is also equivalent to its topological
closure being the whole group. All statements have additive counterparts.
-/

@[expose] public section

universe u

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A dense finitely generated subgroup exists exactly when a finite set generates a
subgroup that is dense. This does not assert that the ambient group is finitely generated. -/
@[to_additive /-- A dense finitely generated additive subgroup exists exactly when a finite
set generates an additive subgroup that is dense. This does not assert that the ambient
additive group is finitely generated. -/]
theorem exists_fg_dense_iff :
    (∃ D : Subgroup G, D.FG ∧ Dense (D : Set G)) ↔
      ∃ S : Finset G, Dense (closure (S : Set G) : Set G) := by
  constructor
  · rintro ⟨D, ⟨S, hS⟩, hD⟩
    exact ⟨S, by simpa only [hS] using hD⟩
  · rintro ⟨S, hS⟩
    exact ⟨closure (S : Set G), ⟨S, rfl⟩, hS⟩

/-- A subgroup of a topological group is dense exactly when its topological closure is the
whole group. -/
@[to_additive /-- An additive subgroup of an additive topological group is dense exactly when
its topological closure is the whole group. -/]
theorem dense_iff_topologicalClosure_eq_top [IsTopologicalGroup G] (D : Subgroup G) :
    Dense (D : Set G) ↔ D.topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff]
  simp only [topologicalClosure_coe, coe_top, dense_iff_closure_eq]

end Subgroup

end
