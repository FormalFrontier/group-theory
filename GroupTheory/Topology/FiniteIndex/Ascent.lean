/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex.Descent
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Profinite

/-!
# Finite-index openness from a kernel and target

Finite-index subgroups of a group are open if this holds for the kernel and target
of a continuous surjective homomorphism, provided the source has an open
finite-index subgroup neighborhood basis. In particular this applies to compact
Hausdorff totally disconnected topological groups.

The lower-level result uses only continuity of fixed left translations on the
source. The target need not be a topological group, and the kernel need not be
closed. The proof uses Mathlib's finite-index subgroup API and its open-subgroup
neighborhood theorem for the profinite specialization.
-/

@[expose] public section

open Set Filter Topology

universe u v

namespace Subgroup

/-- Finite-index openness ascends from a kernel and target when the source has an
open finite-index subgroup neighborhood basis and continuous left translations. -/
theorem isOpen_finiteIndex_of_ker_of_hasBasis
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    [TopologicalSpace G] [TopologicalSpace Q]
    (q : G →* Q) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hleft : ∀ g : G, Continuous (g * ·))
    (hBasis : (𝓝 (1 : G)).HasBasis
      (fun U : Subgroup G => U.FiniteIndex ∧ IsOpen (U : Set G))
      (fun U => (U : Set G)))
    (hker : ∀ H : Subgroup q.ker, H.FiniteIndex → IsOpen (H : Set q.ker))
    (hQ : ∀ H : Subgroup Q, H.FiniteIndex → IsOpen (H : Set Q)) :
    ∀ K : Subgroup G, K.FiniteIndex → IsOpen (K : Set G) := by
  intro K hK
  have : K.FiniteIndex := hK
  have hHfi : (K.comap q.ker.subtype).FiniteIndex := by
    change (K.subgroupOf q.ker).FiniteIndex
    infer_instance
  have hH : IsOpen (K.comap q.ker.subtype : Set q.ker) := hker _ hHfi
  obtain ⟨O, hO, hOH⟩ := isOpen_induced_iff.mp hH
  have h1O : (1 : G) ∈ O := by
    have h1 : (1 : q.ker) ∈ (K.comap q.ker.subtype : Set q.ker) := one_mem _
    rwa [← hOH] at h1
  have hOker : ∀ x ∈ O, x ∈ q.ker → x ∈ K := by
    intro x hx hxker
    have : (⟨x, hxker⟩ : q.ker) ∈ (K.comap q.ker.subtype : Set q.ker) := by
      rw [← hOH]
      exact hx
    exact this
  obtain ⟨U, ⟨hU, hUopen⟩, hUO⟩ := hBasis.mem_iff.mp (hO.mem_nhds h1O)
  have : U.FiniteIndex := hU
  have hKU : (K ⊓ U).FiniteIndex := inferInstance
  have hmap : ((K ⊓ U).map q).FiniteIndex :=
    finiteIndex_iff.mpr (ne_zero_of_dvd_ne_zero (finiteIndex_iff.mp hKU)
      (index_map_dvd (K ⊓ U) hsurj))
  have himage : IsOpen ((K ⊓ U).map q : Set Q) := hQ _ hmap
  have hinter : (U : Set G) ∩ q ⁻¹' ((K ⊓ U).map q : Set Q) = (K ⊓ U : Set G) := by
    ext x
    constructor
    · rintro ⟨hxU, y, hy, hxy⟩
      have hdiffU : y⁻¹ * x ∈ U := U.mul_mem (U.inv_mem hy.2) hxU
      have hdiffker : y⁻¹ * x ∈ q.ker := by
        change q (y⁻¹ * x) = 1
        simp only [map_mul, map_inv, hxy, inv_mul_cancel]
      have hdiffK : y⁻¹ * x ∈ K := hOker _ (hUO hdiffU) hdiffker
      have hxK := K.mul_mem hy.1 hdiffK
      rw [mul_inv_cancel_left] at hxK
      exact ⟨hxK, hxU⟩
    · intro hx
      exact ⟨hx.2, x, hx, rfl⟩
  have hopen : IsOpen (K ⊓ U : Set G) := by
    rw [← hinter]
    exact hUopen.inter (himage.preimage hq)
  have : ContinuousConstSMul G G := ⟨hleft⟩
  apply K.isOpen_iff_mem_nhds_one.mpr
  exact mem_of_superset (hopen.mem_nhds (one_mem (K ⊓ U))) inf_le_left

/-- For a compact Hausdorff totally disconnected topological group, openness of
finite-index subgroups ascends from the kernel and target of any continuous
surjective homomorphism. No topological group structure on the target is needed. -/
theorem isOpen_finiteIndex_of_ker
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    [TopologicalSpace G] [TopologicalSpace Q] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (q : G →* Q) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hker : ∀ H : Subgroup q.ker, H.FiniteIndex → IsOpen (H : Set q.ker))
    (hQ : ∀ H : Subgroup Q, H.FiniteIndex → IsOpen (H : Set Q)) :
    ∀ K : Subgroup G, K.FiniteIndex → IsOpen (K : Set G) := by
  have hBasis : (𝓝 (1 : G)).HasBasis
      (fun U : Subgroup G => U.FiniteIndex ∧ IsOpen (U : Set G))
      (fun U => (U : Set G)) := by
    refine ⟨fun V => ⟨?_, ?_⟩⟩
    · intro hV
      obtain ⟨C, ⟨h1C, hC⟩, hCV⟩ := (nhds_basis_clopen (1 : G)).mem_iff.mp hV
      obtain ⟨U, hUC⟩ :=
        IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hC h1C
      have : Finite (G ⧸ U.toSubgroup) := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
      exact ⟨U.toSubgroup, ⟨finiteIndex_of_finite_quotient, U.isOpen⟩, hUC.trans hCV⟩
    · rintro ⟨U, ⟨_, hUopen⟩, hUV⟩
      exact mem_of_superset (hUopen.mem_nhds U.one_mem) hUV
  exact isOpen_finiteIndex_of_ker_of_hasBasis q hq hsurj
    (fun g => continuous_const.mul continuous_id) hBasis hker hQ

/-- Finite-index openness ascends from a normal subgroup and its quotient in a
compact Hausdorff totally disconnected topological group. The normal subgroup
need not be closed; the quotient has its quotient topology. -/
theorem isOpen_finiteIndex_of_normal
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal]
    (hN : ∀ H : Subgroup N, H.FiniteIndex → IsOpen (H : Set N))
    (hquot : ∀ H : Subgroup (G ⧸ N), H.FiniteIndex → IsOpen (H : Set (G ⧸ N))) :
    ∀ K : Subgroup G, K.FiniteIndex → IsOpen (K : Set G) := by
  apply isOpen_finiteIndex_of_ker (QuotientGroup.mk' N)
    continuous_quot_mk (QuotientGroup.mk'_surjective N) _ hquot
  rw [QuotientGroup.ker_mk']
  exact hN

end Subgroup
