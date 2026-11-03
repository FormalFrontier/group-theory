/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.Maps.Basic

/-!
# Postcomposition of equicontinuous families at a common value

For a family with a common value at a point, continuity at that value suffices for
postcomposition to preserve equicontinuity there. A local neighborhood-reflection
condition gives the converse, and an inducing map provides both directions.
-/

@[expose] public section

open Filter Topology

universe u v w z

variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [UniformSpace Y] [UniformSpace Z]
  {F : A → X → Y} {x₀ : X} {c : Y} {h : Y → Z}

/-- At a common base value, postcomposition preserves equicontinuity under continuity
of the target map at that value. -/
theorem EquicontinuousAt.postcomp_of_eq (hF : EquicontinuousAt F x₀)
    (hbase : ∀ a, F a x₀ = c) (hh : ContinuousAt h c) :
    EquicontinuousAt (fun a x => h (F a x)) x₀ := by
  apply (equicontinuousAt_iff_forall_mem_nhds_of_eq
    (F := fun a x => h (F a x)) (fun a => congrArg h (hbase a))).mpr
  intro t ht
  exact (equicontinuousAt_iff_forall_mem_nhds_of_eq hbase).mp hF
    (h ⁻¹' t) (hh.preimage_mem_nhds ht)

/-- A target map that locally reflects neighborhoods at the common base value reflects
equicontinuity there, without requiring continuity of the target map. -/
theorem EquicontinuousAt.of_postcomp_of_comap_nhds_le_of_eq
    (hF : EquicontinuousAt (fun a x => h (F a x)) x₀)
    (hbase : ∀ a, F a x₀ = c) (hlocal : comap h (𝓝 (h c)) ≤ 𝓝 c) :
    EquicontinuousAt F x₀ := by
  apply (equicontinuousAt_iff_forall_mem_nhds_of_eq hbase).mpr
  intro s hs
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp (hlocal hs)
  have hmem := (equicontinuousAt_iff_forall_mem_nhds_of_eq
    (F := fun a x => h (F a x)) (fun a => congrArg h (hbase a))).mp hF
  exact (hmem t ht).mono fun _ hx a => hts (hx a)

/-- Postcomposition by an inducing map preserves and reflects equicontinuity at a point
where the family has a common value. -/
theorem Topology.IsInducing.equicontinuousAt_iff_of_eq (hh : IsInducing h)
    (hbase : ∀ a, F a x₀ = c) :
    EquicontinuousAt (fun a x => h (F a x)) x₀ ↔ EquicontinuousAt F x₀ := by
  constructor
  · intro hF
    exact hF.of_postcomp_of_comap_nhds_le_of_eq hbase (hh.nhds_eq_comap c).ge
  · intro hF
    exact hF.postcomp_of_eq hbase hh.continuous.continuousAt
