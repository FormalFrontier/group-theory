/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite power control

Compact closed subgroup-free sets control identity neighborhoods.

## References

Mathlib's compactness API.
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
