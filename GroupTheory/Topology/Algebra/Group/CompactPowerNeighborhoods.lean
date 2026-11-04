/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Compactness.Compact
import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups

/-!
# Integer-power control and identity-neighborhood bases

Compact closed subgroup-free sets control identity neighborhoods. A compact
identity-neighborhood containing no nontrivial subgroup yields a countable
antitone basis by testing integer powers of bounded absolute value. Its
closedness follows from the no-small-subgroups separation theorem.

## References

Mathlib's compactness and filter APIs, and the no-small-subgroups development.
-/

@[expose] public section

/-- If a compact closed set contains no nontrivial subgroup, bounded integer-power tests
in it uniformly force membership in any identity neighborhood. -/
theorem IsCompact.exists_nat_forall_zpow_mem_imp_mem
    {D : Type*} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    {K U : Set D} (hK : IsCompact K) (hK_closed : IsClosed K)
    (hK_subgroup : ∀ H : Subgroup D, (H : Set D) ⊆ K → H = ⊥)
    (hU : U ∈ nhds (1 : D)) :
    ∃ N : ℕ, ∀ x : D, (∀ n : ℤ, n.natAbs ≤ N → x ^ n ∈ K) → x ∈ U
:= by
  classical
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hV_open, hV_one⟩
  have hopen (n : ℤ) : IsOpen {x : D | x ^ n ∉ K} :=
    hK_closed.isOpen_compl.preimage (continuous_zpow n)
  have hcover : K \ V ⊆ ⋃ n : ℤ, {x : D | x ^ n ∉ K} := by
    intro x hx
    by_contra h
    have hpow (n : ℤ) : x ^ n ∈ K := by
      by_contra hn
      exact h (Set.mem_iUnion.mpr ⟨n, hn⟩)
    have hcyc : Subgroup.zpowers x = ⊥ := hK_subgroup _ (by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact hpow n)
    have hx1 : x = 1 := by
      have hxmem := Subgroup.mem_zpowers x
      rw [hcyc] at hxmem
      simpa using hxmem
    exact hx.2 (by simpa only [hx1] using hV_one)
  rcases (hK.diff hV_open).elim_finite_subcover
      (fun n : ℤ => {x : D | x ^ n ∉ K}) hopen hcover with ⟨s, hs⟩
  refine ⟨max 1 (s.sup Int.natAbs), ?_⟩
  intro x hx
  have hxK : x ∈ K := by
    have h1 : (1 : ℤ).natAbs ≤ max 1 (s.sup Int.natAbs) := by
      simp
    simpa using hx 1 h1
  by_contra hxU
  have hxV : x ∉ V := fun hxV => hxU (hVU hxV)
  rcases Set.mem_iUnion.mp (hs ⟨hxK, hxV⟩) with ⟨n, hn⟩
  rcases Set.mem_iUnion.mp hn with ⟨hns, hxn⟩
  exact hxn (hx n (le_trans (Finset.le_sup (f := Int.natAbs) hns)
    (le_max_right 1 (s.sup Int.natAbs))))

universe u

open scoped Topology

/-- A compact identity-neighborhood containing no nontrivial subgroup gives a
countable antitone basis at the identity by bounded integer-power tests. -/
theorem IsCompact.hasAntitoneBasis_nhds_one_zpow_mem
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Set G} (hK : IsCompact K) (hK_nhds : K ∈ 𝓝 (1 : G))
    (hK_subgroup : ∀ H : Subgroup G, (H : Set G) ⊆ K → H = ⊥) :
    Filter.HasAntitoneBasis (𝓝 (1 : G))
      (fun N : ℕ => {x : G | ∀ n : ℤ, n.natAbs ≤ N + 1 → x ^ n ∈ K}) := by
  let : NoSmallSubgroups G := noSmallSubgroups_iff.mpr ⟨K, hK_nhds, hK_subgroup⟩
  let : T2Space G := NoSmallSubgroups.t2Space (G := G)
  have hW (N : ℕ) :
      {x : G | ∀ n : ℤ, n.natAbs ≤ N + 1 → x ^ n ∈ K} ∈ 𝓝 (1 : G) := by
    have hpow (n : ℤ) : {x : G | x ^ n ∈ K} ∈ 𝓝 (1 : G) := by
      have hc : ContinuousAt (fun x : G => x ^ n) (1 : G) :=
        (continuous_zpow n).continuousAt
      exact hc.preimage_mem_nhds (by simpa only [one_zpow] using hK_nhds)
    have hpos : ∀ᶠ x in 𝓝 (1 : G), ∀ i : Fin (N + 2), x ^ (i.val : ℤ) ∈ K :=
      Filter.eventually_all.mpr (fun i => hpow (i.val : ℤ))
    have hneg : ∀ᶠ x in 𝓝 (1 : G), ∀ i : Fin (N + 1), x ^ (Int.negSucc i.val) ∈ K :=
      Filter.eventually_all.mpr (fun i => hpow (Int.negSucc i.val))
    exact (hpos.and hneg).mono fun x hx n hn => by
      cases n with
      | ofNat n => exact hx.1 ⟨n, Nat.lt_succ_of_le hn⟩
      | negSucc n => exact hx.2 ⟨n, hn⟩
  refine ⟨⟨?_⟩, ?_⟩
  · intro U
    constructor
    · intro hU
      obtain ⟨M, hM⟩ := hK.exists_nat_forall_zpow_mem_imp_mem hK.isClosed hK_subgroup hU
      refine ⟨M, trivial, ?_⟩
      intro x hx
      exact hM x (fun n hn => hx n (le_trans hn (Nat.le_succ M)))
    · rintro ⟨N, _, hNU⟩
      exact Filter.mem_of_superset (hW N) hNU
  · intro N M hNM x hx n hn
    exact hx n (le_trans hn (Nat.add_le_add_right hNM 1))
