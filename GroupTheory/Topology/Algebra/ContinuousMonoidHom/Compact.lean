/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The compact-open/Ascoli argument adapts Mathlib's formalization:
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Nailin Guan
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Compact bounded families of homomorphisms

For a compact topological group `T`, a closed set `W` containing no nontrivial
subgroup controls compact families of continuous homomorphisms: the homomorphisms
mapping an identity-neighborhood `U` into `W` form a compact set in the original
compact-open topology. Neither group needs to be commutative or Hausdorff.

Consequently, if `G` is locally compact and `T` is compact with no small subgroups,
`G →ₜ* T` is locally compact as a space. For noncommutative `T` this hom space is
not generally a group. Each homomorphism receives its own compact neighborhood.

## Proof and formalization credits

Finite integer-power tests on the compact target give equicontinuity of all the
bounded algebraic homomorphisms. We then use Mathlib's closed algebraic-hom locus,
Arzela-Ascoli theorem, and canonical compact-open embedding. The latter composition
follows Thomas Browning and Nailin Guan's compact-open hom formalization, using
Anatole Dedecker's equicontinuity/Ascoli work and the topological-group and uniform
space infrastructure of Johannes Hölzl, Patrick Massot and collaborators.
-/

public section

open Set Filter Topology

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {T : Type v}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [CompactSpace T]

/-- Compactness extracts finitely many integer powers detecting membership in any
identity-neighborhood from a closed set containing no nontrivial subgroup. -/
private theorem exists_finset_zpow_tests {W V : Set T} (hW : IsClosed W)
    (hsub : ∀ H : Subgroup T, (H : Set T) ⊆ W → H = ⊥) (hV : V ∈ 𝓝 (1 : T)) :
    ∃ F : Finset ℤ, ∀ t : T, (∀ n ∈ F, t ^ n ∈ W) → t ∈ V := by
  classical
  obtain ⟨O, hOV, hO, hO1⟩ := mem_nhds_iff.mp hV
  let A : ℤ → Set T := fun n => {t | t ^ n ∉ W}
  have hA : ∀ n, IsOpen (A n) := fun n =>
    hW.isOpen_compl.preimage (continuous_zpow n)
  have hcover : Oᶜ ⊆ ⋃ n, A n := by
    intro t ht
    by_contra h
    have hZW : (Subgroup.zpowers t : Set T) ⊆ W := by
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      by_contra hn
      exact h (mem_iUnion.mpr ⟨n, hn⟩)
    have ht1 : t = 1 := Subgroup.zpowers_eq_bot.mp (hsub _ hZW)
    exact ht (ht1.symm ▸ hO1)
  obtain ⟨F, hF⟩ := hO.isClosed_compl.isCompact.elim_finite_subcover A hA hcover
  refine ⟨F, fun t ht => hOV ?_⟩
  by_contra hnot
  obtain ⟨n, hn, hnt⟩ := mem_iUnion₂.mp (hF hnot)
  exact hnt (ht n hn)

/-- Identity equicontinuity applies even to algebraic homomorphisms: continuity
of the individual bounded homomorphisms will follow from equicontinuity. -/
private theorem equicontinuousAt_one_setOf_mapsTo
    {G : Type u} {T : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group T] [UniformSpace T] [IsUniformGroup T] [CompactSpace T]
    {U : Set G} {W : Set T} (hU : U ∈ 𝓝 (1 : G)) (hW : IsClosed W)
    (hsub : ∀ H : Subgroup T, (H : Set T) ⊆ W → H = ⊥) :
    EquicontinuousAt (fun f : {f : G →* T | MapsTo f U W} => (f : G → T)) 1 := by
  rw [(𝓝 (1 : T)).basis_sets.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  intro V hV
  obtain ⟨F, hF⟩ := exists_finset_zpow_tests hW hsub hV
  have hpow (n : ℤ) : ∀ᶠ x in 𝓝 (1 : G), x ^ n ∈ U := by
    have hz : Tendsto (fun x : G => x ^ n) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
      simpa only [one_zpow] using (continuous_zpow n).tendsto (1 : G)
    exact hz hU
  have hP : ∀ᶠ x in 𝓝 (1 : G), ∀ n ∈ F, x ^ n ∈ U :=
    (Filter.eventually_all_finset F).mpr fun n _ => hpow n
  filter_upwards [hP] with x hx
  intro f
  change f.val x / f.val 1 ∈ V
  simp only [map_one, div_one]
  apply hF
  intro n hn
  rw [← map_zpow]
  exact f.property (hx n hn)

/-- Homomorphisms mapping an identity-neighborhood into a closed set containing
no nontrivial subgroup form a compact set in the compact-open topology.

The target group is compact, but need not be commutative or assumed Hausdorff.
The control set `W` need not itself be an identity-neighborhood. -/
theorem isCompact_setOf_mapsTo {U : Set G} {W : Set T} (hU : U ∈ 𝓝 (1 : G))
    (hW : IsClosed W) (hsub : ∀ H : Subgroup T, (H : Set T) ⊆ W → H = ⊥) :
    IsCompact {f : G →ₜ* T | MapsTo f U W} := by
  classical
  by_cases hW1 : (1 : T) ∈ W
  · let : T2Space T := hW.t2Space_of_subgroup_eq_bot hW1 hsub
    -- This uniformity extends exactly the original topology; compactness supplies
    -- IsUniformGroup, without a commutativity hypothesis.
    let : UniformSpace T := IsTopologicalGroup.rightUniformSpace T
    let S1 : Set (G →* T) := {f | MapsTo f U W}
    let S2 : Set (G →ₜ* T) := {f | MapsTo f U W}
    let S3 : Set C(G, T) := toContinuousMap '' S2
    let S4 : Set (G → T) := ContinuousMap.toFun '' S3
    have h : Equicontinuous ((↑) : S1 → G → T) :=
      equicontinuous_of_equicontinuousAt_one (fun f : S1 => f.val)
        (equicontinuousAt_one_setOf_mapsTo hU hW hsub)
    have hS4 : S4 = ((↑) : (G →* T) → G → T) '' S1 := by
      ext f
      constructor
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨g, hg, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, h.continuous ⟨g, hg⟩⟩,
          ⟨⟨g, h.continuous ⟨g, hg⟩⟩, hg, rfl⟩, rfl⟩
    have hS3 : Equicontinuous ((↑) : S3 → G → T) := by
      rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
      rwa [← hS4] at h
    have hclosed : IsClosed S4 := by
      have hlocus : S4 = Set.pi U (fun _ => W) ∩
          Set.range ((↑) : (G →* T) → G → T) := by
        rw [hS4]
        ext f
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact ⟨hg, g, rfl⟩
        · rintro ⟨hg, g, rfl⟩
          exact ⟨g, hg, rfl⟩
      rw [hlocus]
      exact (isClosed_set_pi (fun _ _ => hW)).inter (MonoidHom.isClosed_range_coe G T)
    exact (isInducing_toContinuousMap G T).isCompact_iff.mpr
      (ArzelaAscoli.isCompact_of_equicontinuous S3 hclosed.isCompact hS3)
  · have hempty : {f : G →ₜ* T | MapsTo f U W} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro f hf
      exact hW1 (by simpa only [map_one] using hf (mem_of_mem_nhds hU))
    rw [hempty]
    exact isCompact_empty

/-- For a locally compact topological group `G` and a compact topological group `T`
with no small subgroups, the original compact-open space `G →ₜ* T` is locally
compact. Neither group is required to be commutative or the source Hausdorff. -/
instance locallyCompactSpace_of_noSmallSubgroups [LocallyCompactSpace G]
    [NoSmallSubgroups T] : LocallyCompactSpace (G →ₜ* T) := by
  obtain ⟨W, hW, hWclosed, hsub⟩ := NoSmallSubgroups.exists_isClosed_nhds_one (G := T)
  let : WeaklyLocallyCompactSpace (G →ₜ* T) := {
    exists_compact_mem_nhds := fun f => by
      have hf_one : f.toContinuousMap (1 : G) = (1 : T) := _root_.map_one f
      have hfW : f ⁻¹' interior W ∈ 𝓝 (1 : G) :=
        f.continuous.continuousAt (by
          simpa only [hf_one] using interior_mem_nhds.mpr hW)
      obtain ⟨K, hK, hKf, hKcompact⟩ := local_compact_nhds hfW
      refine ⟨{g : G →ₜ* T | MapsTo g K W},
        isCompact_setOf_mapsTo hK hWclosed hsub, ?_⟩
      have hopen : IsOpen {g : G →ₜ* T | MapsTo g K (interior W)} :=
        isOpen_induced (ContinuousMap.isOpen_setOfPred_mapsTo hKcompact isOpen_interior)
      exact mem_of_superset (hopen.mem_nhds hKf)
        (fun g hg => hg.mono_right interior_subset) }
  infer_instance

end ContinuousMonoidHom
