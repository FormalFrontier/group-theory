/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Maps.OpenQuotient
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact lifts along continuous open maps

A compact lift of a set `K : Set Y` along `f : X → Y` is a compact set `L : Set X` such that
`f '' L = K`. For a continuous open map from a weakly locally compact space, every compact
closed set contained in the range has such a lift. The spaces `X` and `Y` may have independent
universes and carry their original topologies.

## Main results

* `IsCompact.exists_compact_lift_of_isOpenMap` gives a compact lift of a compact closed set
  contained in the range of a continuous open map.
* `IsOpenQuotientMap.exists_compact_lift` gives a compact lift of every compact subset of a
  Hausdorff target of an open quotient map with weakly locally compact source.

A compact lift is only a compact subset of `f ⁻¹' K`; the whole inverse image need not be
compact. In particular, no compactness of the fibres or continuous section is required.

## References

The compact-neighborhood and finite-subcover approach follows the Mathlib community's
formalization in `Mathlib.Topology.Compactness.LocallyCompact` and
`Mathlib.Topology.Compactness.Compact`, including finite compact unions and intersections
with closed sets. The open quotient map API is from `Mathlib.Topology.Maps.OpenQuotient`;
the Hausdorff compact-closedness implication is from `Mathlib.Topology.Separation.Hausdorff`.
-/

@[expose] public section

open Set

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A compact closed set contained in the range of a continuous open map from a weakly
locally compact space has a compact lift. This gives a compact subset of the inverse image,
not compactness of the whole inverse image. -/
theorem IsCompact.exists_compact_lift_of_isOpenMap [WeaklyLocallyCompactSpace X]
    {f : X → Y} {K : Set Y} (hK : IsCompact K) (hK_closed : IsClosed K)
    (hf : Continuous f) (hf_open : IsOpenMap f) (hK_range : K ⊆ Set.range f) :
    ∃ L : Set X, IsCompact L ∧ f '' L = K := by
  classical
  have hlocal : ∀ x : X, ∃ C : Set X, IsCompact C ∧ x ∈ interior C := by
    intro x
    obtain ⟨C, hC, hxC⟩ :=
      exists_compact_superset (isCompact_singleton : IsCompact ({x} : Set X))
    exact ⟨C, hC, hxC (by simp)⟩
  choose C hC hxC using hlocal
  have hcover : K ⊆ ⋃ x : X, f '' interior (C x) := by
    intro y hy
    obtain ⟨x, rfl⟩ := hK_range hy
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_image_of_mem f (hxC x)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : X ↦ f '' interior (C x))
    (fun x ↦ hf_open _ isOpen_interior) hcover
  refine ⟨(⋃ x ∈ s, C x) ∩ f ⁻¹' K, ?_, ?_⟩
  · exact (s.isCompact_biUnion (fun x _ ↦ hC x)).inter_right (hK_closed.preimage hf)
  · apply Set.Subset.antisymm
    · rintro y ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hy)
      obtain ⟨hxs, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨z, ⟨Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxs, interior_subset hz⟩⟩,
        hy⟩, rfl⟩

/-- Every compact subset of the Hausdorff target of an open quotient map from a weakly
locally compact space has a compact lift. -/
theorem IsOpenQuotientMap.exists_compact_lift [WeaklyLocallyCompactSpace X] [T2Space Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) {K : Set Y} (hK : IsCompact K) :
    ∃ L : Set X, IsCompact L ∧ f '' L = K := by
  exact hK.exists_compact_lift_of_isOpenMap hK.isClosed hf.continuous hf.isOpenMap
    (fun y _ ↦ hf.surjective y)
