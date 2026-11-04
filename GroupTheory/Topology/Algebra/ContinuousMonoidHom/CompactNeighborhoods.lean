/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMap.CompactNeighborhoods
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Compact bounds for continuous monoid homomorphisms

A compact-open neighborhood of a continuous monoid homomorphism can impose a
prescribed identity-neighborhood bound on a compact source neighborhood and a
compact target bound on any specified compact source set.

This is the continuous-map compact-bounds theorem at the identity, pulled back
along `ContinuousMonoidHom.toContinuousMap`. The monoid operations need not be
continuous, and no separation axiom is required.

## References

The proof specializes `ContinuousMap.exists_isCompact_bounds_mem_nhds` using
Mathlib's `ContinuousMonoidHom.isInducing_toContinuousMap`.
-/

@[expose] public section

open Set Filter Topology

universe u v

/-- For any identity neighborhood `K` and compact source set `s`, there are a compact
identity neighborhood `Q` and a compact target set `P` such that the continuous monoid
homomorphisms sending `Q` into `K` and `s` into `P` form a neighborhood of `f₀` in the
compact-open topology. No continuity of the monoid operations is assumed. -/
theorem ContinuousMonoidHom.exists_isCompact_bounds_mem_nhds
    {M : Type u} {D : Type v}
    [Monoid M] [TopologicalSpace M] [LocallyCompactSpace M]
    [Monoid D] [TopologicalSpace D] [WeaklyLocallyCompactSpace D]
    (f₀ : M →ₜ* D) (s : Set M) (hs : IsCompact s)
    (K : Set D) (hK : K ∈ nhds (1 : D)) :
    ∃ Q : Set M, Q ∈ nhds (1 : M) ∧ IsCompact Q ∧
      ∃ P : Set D, IsCompact P ∧
        {f : M →ₜ* D | Set.MapsTo f Q K ∧ Set.MapsTo f s P} ∈ nhds f₀ := by
  have hK' : K ∈ nhds (f₀.toContinuousMap (1 : M)) := by
    change K ∈ nhds (f₀ (1 : M))
    simpa only [map_one] using hK
  obtain ⟨Q, hQ, hQc, P, hPc, hN⟩ :=
    ContinuousMap.exists_isCompact_bounds_mem_nhds f₀.toContinuousMap (1 : M) s hs K hK'
  refine ⟨Q, hQ, hQc, P, hPc, ?_⟩
  -- Pull back the same bounds through the compact-open projection, keeping Q and P.
  have hprojection :
      Continuous (ContinuousMonoidHom.toContinuousMap : (M →ₜ* D) → C(M, D)) :=
    (ContinuousMonoidHom.isInducing_toContinuousMap M D).continuous
  exact hprojection.continuousAt.preimage_mem_nhds hN
