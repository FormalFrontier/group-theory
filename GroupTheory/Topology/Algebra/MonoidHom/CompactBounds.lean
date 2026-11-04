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
from a set to its closure under one and multiplication, or to its subgroup
closure. The bound may vary with the source element. No topology on the source
or index type is required.
-/

@[expose] public section

universe u v w z

namespace MonoidHomClass

variable {M : Type u} {D : Type v} {ι : Type w} {F : Type z}
variable [MulOneClass M] [MulOneClass D] [TopologicalSpace D] [ContinuousMul D]
variable [FunLike F M D] [MonoidHomClass F M D]

/-- Compact bounds for a family of maps preserving one and multiplication
propagate to the closure under these operations. No associativity is required.
For subgroup closures, see `MonoidHom.exists_isCompact_bound_of_mem_closure`. -/
theorem exists_isCompact_bound_of_mem_submonoid_closure
    (f : ι → F) {s : Set M}
    (hbound : ∀ x ∈ s, ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K)
    {x : M} (hx : x ∈ Submonoid.closure s) :
    ∃ K : Set D, IsCompact K ∧ ∀ i, f i x ∈ K := by
  let P : Submonoid M :=
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
        exact ⟨(f i a, f i b), ⟨ha i, hb i⟩, (map_mul (f i) a b).symm⟩ }
  have hsP : s ⊆ (P : Set M) := by
    intro a ha
    exact hbound a ha
  exact (Submonoid.closure_le.mpr hsP) hx

end MonoidHomClass

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
  let t : Set G := s ∪ (fun a : G => a⁻¹) '' s
  have ht : ∀ y ∈ t, ∃ K : Set D, IsCompact K ∧ ∀ i, f i y ∈ K := by
    intro y hy
    rcases hy with hy | ⟨a, ha, rfl⟩
    · exact hbound y hy
    · obtain ⟨K, hK, hf⟩ := hbound a ha
      refine ⟨(fun d : D => d⁻¹) '' K, hK.image continuous_inv, ?_⟩
      intro i
      rw [map_inv]
      exact ⟨f i a, hf i, rfl⟩
  have hx' : x ∈ Submonoid.closure t ∧ x⁻¹ ∈ Submonoid.closure t := by
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact ⟨Submonoid.subset_closure (Or.inl hy),
        Submonoid.subset_closure (Or.inr ⟨y, hy, rfl⟩)⟩
    · refine ⟨(Submonoid.closure t).one_mem, ?_⟩
      simpa only [inv_one] using (Submonoid.closure t).one_mem
    · intro a b _ _ ha hb
      refine ⟨(Submonoid.closure t).mul_mem ha.1 hb.1, ?_⟩
      simpa only [mul_inv_rev] using
        (Submonoid.closure t).mul_mem hb.2 ha.2
    · intro a _ ha
      exact ⟨ha.2, by simpa only [inv_inv] using ha.1⟩
  exact MonoidHomClass.exists_isCompact_bound_of_mem_submonoid_closure
    (M := G) (F := G →* D) f ht hx'.1

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
