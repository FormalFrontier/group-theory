/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact bounds on families of homomorphisms

Compact bounds on the values of an indexed family of homomorphisms propagate
from a set to its algebraic subgroup closure. The bound may vary with the source
element. No topology on the source group or index type is required.
-/

@[expose] public section

universe u v w

namespace MonoidHom

variable {G : Type u} {D : Type v} {ι : Type w}
variable [Group G] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]

/-- Compact bounds for the values of a family of homomorphisms propagate to
any element of the algebraic subgroup closure of the bounded set. -/
theorem exists_isCompact_bound_of_mem_closure
    (f : ι → G →* D) {s : Set G}
    (hbound : ∀ x ∈ s, ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K)
    {x : G} (hx : x ∈ Subgroup.closure s) :
    ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K := by
  let P : Subgroup G :=
    { carrier := {a | ∃ K : Set D, IsCompact K ∧ ∀ i, f i a ∈ K}
      one_mem' := by
        refine ⟨{1}, isCompact_singleton, ?_⟩
        intro i
        exact Set.mem_singleton_iff.mpr (map_one (f i))
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨A, hA, ha⟩
        rcases hb with ⟨B, hB, hb⟩
        refine ⟨(fun p : D × D => p.1 * p.2) '' (A ×ˢ B),
          (hA.prod hB).image (continuous_fst.mul continuous_snd), ?_⟩
        intro i
        exact ⟨(f i a, f i b), ⟨ha i, hb i⟩, (map_mul (f i) a b).symm⟩
      inv_mem' := by
        intro a ha
        rcases ha with ⟨A, hA, ha⟩
        refine ⟨(fun d : D => d⁻¹) '' A, hA.image continuous_inv, ?_⟩
        intro i
        exact ⟨f i a, ha i, (map_inv (f i) a).symm⟩ }
  have hsP : s ⊆ (P : Set G) := by
    intro a ha
    exact hbound a ha
  have hclosure : Subgroup.closure s ≤ P := (Subgroup.closure_le P).mpr hsP
  exact hclosure hx

/-- Compact bounds on an algebraic generating set bound the family at every
source element. Each element can have its own compact bound. -/
theorem exists_isCompact_bound_of_closure_eq_top
    (f : ι → G →* D) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (hbound : ∀ x ∈ s, ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K)
    (x : G) : ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K := by
  apply exists_isCompact_bound_of_mem_closure f hbound
  rw [hs]
  trivial

end MonoidHom
