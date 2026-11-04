/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.CompactPowerNeighborhoods
public import Mathlib.Data.Int.Interval

/-! # Common neighborhood control for algebraic group homomorphisms -/

@[expose] public section

open Filter Topology

universe u v

/-- A common compact closed subgroup-free bound gives common control at the identity. -/
theorem MonoidHom.exists_nhds_one_forall_mapsTo
    {G : Type u} {D : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    {S : Set (G →* D)} {Q : Set G} {K : Set D}
    (hQ : Q ∈ nhds (1 : G)) (hK : IsCompact K) (hK_closed : IsClosed K)
    (hK_subgroup : ∀ H : Subgroup D, (H : Set D) ⊆ K → H = ⊥)
    (hS : ∀ f ∈ S, Set.MapsTo f Q K)
    {V : Set D} (hV : V ∈ nhds (1 : D)) :
    ∃ U ∈ nhds (1 : G), ∀ f ∈ S, Set.MapsTo f U V := by
  classical
  obtain ⟨N, hN⟩ := hK.exists_nat_forall_zpow_mem_imp_mem hK_closed hK_subgroup hV
  have hpow (n : ℤ) : ∀ᶠ x : G in nhds 1, x ^ n ∈ Q := by
    have hc : Tendsto (fun x : G => x ^ n) (nhds 1) (nhds 1) := by
      simpa only [one_zpow] using (continuous_zpow n).tendsto (1 : G)
    exact hc.eventually hQ
  have hfinite (s : Finset ℤ) :
      ∀ᶠ x : G in nhds 1, ∀ n ∈ s, x ^ n ∈ Q := by
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (by simp)
    | @insert n s _ ih =>
      apply ((hpow n).and ih).mono
      intro x hx m hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact hx.1
      · exact hx.2 m hm
  refine ⟨{x | ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), x ^ n ∈ Q}, hfinite _, ?_⟩
  intro f hf x hx
  apply hN (f x)
  intro n hn
  have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr hn
  have hnIcc : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    apply Finset.mem_Icc.mpr
    rcases Int.natAbs_eq n with h | h
    · rw [h]
      exact ⟨le_trans (neg_nonpos.mpr (Int.natCast_nonneg N))
        (Int.natCast_nonneg _), hcast⟩
    · rw [h]
      exact ⟨Int.neg_le_neg hcast,
        le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg N)⟩
  simpa using hS f hf (hx n hnIcc)
