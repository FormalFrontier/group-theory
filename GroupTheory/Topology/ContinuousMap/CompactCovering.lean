/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Compact-covering maps and precomposition

Precomposition by a continuous map that lifts every compact set to an exact compact image is
an embedding for the compact-open topologies. Quotientness is not needed for this assertion.
-/

@[expose] public section

open Set Filter Topology
open scoped Topology

universe u v w

namespace ContinuousMap

/-- Precomposition by a continuous compact-covering map is an embedding for the compact-open
 topologies. Here compact-covering means that every compact set is the exact image of a compact
 set; no quotient-map or separation hypothesis is required. -/
theorem isEmbedding_precomp_of_compactCovering
    {X : Type u} {Y : Type v} {T : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    (q : C(X, Y))
    (hcompact : ∀ K : Set Y, IsCompact K → ∃ L : Set X, IsCompact L ∧ q '' L = K) :
    Topology.IsEmbedding (fun f : C(Y, T) => f.comp q) := by
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨L, _, hL⟩ := hcompact {y} isCompact_singleton
    have hy : y ∈ q '' L := hL.symm ▸ Set.mem_singleton y
    obtain ⟨x, _, hx⟩ := hy
    exact ⟨x, hx⟩
  refine ⟨?_, ?_⟩
  · apply Topology.isInducing_iff_nhds.mpr
    intro f
    apply le_antisymm
    · exact Filter.tendsto_iff_comap.mp (continuous_precomp q).continuousAt
    · have hlim : Filter.Tendsto (fun g : C(Y, T) => g)
          (Filter.comap (fun g : C(Y, T) => g.comp q) (𝓝 (f.comp q))) (𝓝 f) := by
        apply tendsto_nhds_compactOpen.mpr
        intro K hK U hU hmap
        obtain ⟨L, hL, hLK⟩ := hcompact K hK
        have hmapL : MapsTo (f.comp q) L U := by
          intro x hx
          exact hmap (hLK ▸ Set.mem_image_of_mem q hx)
        change {g : C(Y, T) | MapsTo g K U} ∈
          Filter.comap (fun g : C(Y, T) => g.comp q) (𝓝 (f.comp q))
        apply Filter.mem_comap.mpr
        refine ⟨{g : C(X, T) | MapsTo g L U}, eventually_mapsTo hL hU hmapL, ?_⟩
        intro g hg y hy
        have hyL : y ∈ q '' L := hLK.symm ▸ hy
        obtain ⟨x, hx, rfl⟩ := hyL
        exact hg hx
      exact Filter.tendsto_id'.mp hlim
  · intro f g hfg
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    exact congrArg (fun h : C(X, T) => h x) hfg

end ContinuousMap
