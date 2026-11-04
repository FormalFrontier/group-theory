/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/

module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Compact bounds in compact-open neighborhoods

For a continuous map from a locally compact space to a weakly locally compact space,
we can simultaneously control its values near a specified source point and on a
specified compact set. The resulting family is a neighborhood in the compact-open
topology.

The argument uses open constraints with targets `interior K` and `interior P`;
it does not require compact sets to be closed or either space to be Hausdorff.

## References

The proof combines Mathlib's compact-neighborhood results `exists_compact_subset`
and `exists_compact_superset` with `ContinuousMap.isOpen_setOfPred_mapsTo`.
-/

@[expose] public section

open Set Filter Topology

universe u v

/-- Given a neighborhood `K` of `f₀ x₀` and a compact source set `s`, there are a compact
neighborhood `Q` of `x₀` and a compact target set `P` such that the continuous maps
sending `Q` into `K` and `s` into `P` form a neighborhood of `f₀` in the compact-open
topology. Only weak local compactness is needed in the target. -/
theorem ContinuousMap.exists_isCompact_bounds_mem_nhds
    {M : Type u} {D : Type v}
    [TopologicalSpace M] [LocallyCompactSpace M]
    [TopologicalSpace D] [WeaklyLocallyCompactSpace D]
    (f₀ : C(M, D)) (x₀ : M)
    (s : Set M) (hs : IsCompact s)
    (K : Set D) (hK : K ∈ nhds (f₀ x₀)) :
    ∃ Q : Set M, Q ∈ nhds x₀ ∧ IsCompact Q ∧
      ∃ P : Set D, IsCompact P ∧
        {f : C(M, D) | Set.MapsTo f Q K ∧ Set.MapsTo f s P} ∈ nhds f₀ := by
  have hx₀ : x₀ ∈ f₀ ⁻¹' interior K :=
    mem_interior_iff_mem_nhds.mpr hK
  obtain ⟨Q, hQc, hxQ, hQsub⟩ :=
    exists_compact_subset (isOpen_interior.preimage f₀.continuous) hx₀
  -- Enclose the compact image in an interior; no closedness or separation is needed.
  obtain ⟨P, hPc, hsP⟩ := exists_compact_superset (hs.image f₀.continuous)
  refine ⟨Q, mem_interior_iff_mem_nhds.mp hxQ, hQc, P, hPc, ?_⟩
  have hQopen : IsOpen {f : C(M, D) | MapsTo f Q (interior K)} :=
    ContinuousMap.isOpen_setOfPred_mapsTo hQc isOpen_interior
  have hsopen : IsOpen {f : C(M, D) | MapsTo f s (interior P)} :=
    ContinuousMap.isOpen_setOfPred_mapsTo hs isOpen_interior
  have hN :
      {f : C(M, D) | MapsTo f Q (interior K) ∧ MapsTo f s (interior P)} ∈ nhds f₀ :=
    (hQopen.inter hsopen).mem_nhds ⟨hQsub, fun x hx => hsP ⟨x, hx, rfl⟩⟩
  -- The two open constraints give a smaller neighborhood than the requested bounds.
  exact Filter.mem_of_superset hN fun f hf =>
    ⟨fun x hx => interior_subset (hf.1 hx), fun x hx => interior_subset (hf.2 hx)⟩
