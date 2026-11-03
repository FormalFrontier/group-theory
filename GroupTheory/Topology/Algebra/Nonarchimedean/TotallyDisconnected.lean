/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Connected

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Topology.Separation.Profinite
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Open subgroups of totally disconnected locally compact groups

Van Dantzig's theorem gives a basis of open subgroups at the identity of a totally disconnected
locally compact group. Here weak local compactness suffices: total disconnectedness and the
compatible right uniformity supply the separation properties needed to obtain local compactness.
All these properties concern the given topology.

The proof uses Mathlib's clopen-basis theorem and compact-set multiplication separation. The
stabilizer of a compact clopen identity-neighborhood under left translation is an open subgroup
contained in that neighborhood. Only the original group acts; no topology on its set of subsets
is needed.

## References

* Van Dantzig's theorem on open subgroups of totally disconnected locally compact groups.
* Mathlib's `Topology.Separation.Profinite`, `Topology.Algebra.Group.Basic`, and
  `GroupTheory.GroupAction.Defs`, for the clopen-basis, compact-set separation, and stabilizer
  approaches used here.
-/

@[expose] public section

open Set Filter Topology
open scoped Pointwise

universe u

/-- A weakly locally compact, totally disconnected topological group is nonarchimedean.
This is van Dantzig's open-subgroup theorem. -/
theorem TotallyDisconnectedSpace.nonarchimedeanGroup
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] [WeaklyLocallyCompactSpace G] :
    NonarchimedeanGroup G := by
  -- The right uniformity extends the given topology, so its regularity applies to that topology.
  have : RegularSpace G := by
    let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    infer_instance
  have : T2Space G := inferInstance
  have : LocallyCompactSpace G := inferInstance
  refine { is_nonarchimedean := ?_ }
  intro U hU
  obtain ⟨K, hK, hKnhds⟩ :=
    WeaklyLocallyCompactSpace.exists_compact_mem_nhds (1 : G)
  obtain ⟨C, hC, hC1, hCUK⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp (inter_mem hU hKnhds)
  have hCcompact : IsCompact C :=
    hK.of_isClosed_subset hC.1 (fun x hx ↦ (hCUK hx).2)
  obtain ⟨V, hV, hVC⟩ := compact_open_separated_mul_left hCcompact hC.2 Subset.rfl
  let H : Subgroup G := MulAction.stabilizer G C
  -- Both a translation and its inverse preserve C in one direction, hence stabilize C.
  have hWH : V ∩ V⁻¹ ⊆ (H : Set G) := by
    intro w hw
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subset.antisymm
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := mem_smul_set.mp hx
      simpa only [smul_eq_mul] using hVC (mul_mem_mul hw.1 hc)
    · intro x hx
      refine mem_smul_set.mpr ⟨w⁻¹ * x, hVC (mul_mem_mul (mem_inv.mp hw.2) hx), ?_⟩
      simp only [smul_eq_mul, mul_inv_cancel_left]
  have hHnhds : (H : Set G) ∈ 𝓝 (1 : G) :=
    mem_of_superset (inter_mem hV (inv_mem_nhds_one G hV)) hWH
  refine ⟨{ toSubgroup := H, isOpen' := H.isOpen_of_mem_nhds hHnhds }, ?_⟩
  intro h hh
  have hfix : h • C = C := MulAction.mem_stabilizer_iff.mp hh
  have hhC : h • (1 : G) ∈ h • C := smul_mem_smul_set hC1
  rw [hfix] at hhC
  exact (hCUK (by simpa only [smul_eq_mul, mul_one] using hhC)).1
