/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.Subgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Connected commutator subgroups

A mixed commutator subgroup is connected when its second factor is preconnected
and every commutator section in that factor is continuous. The ambient group
needs only continuous left translations. The proof uses the identity component
inside the commutator subgroup, with its inherited group structure and topology.

## References

- Mathlib, `Subgroup.commutator_le` and `IsPreconnected.subset_connectedComponent`.
- `Subgroup.connectedComponentOfOneOfContinuousConstSMul`.
-/

@[expose] public section

open scoped commutatorElement

universe u

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- A mixed commutator subgroup is connected if its second factor is preconnected
and each commutator section in that factor is continuous. -/
theorem isConnected_commutator_of_isPreconnected_right
    (K H : Subgroup G) (hH : IsPreconnected (H : Set G))
    (hcomm : ∀ g ∈ K, ContinuousOn (fun h : G ↦ ⁅g, h⁆) (H : Set G)) :
    IsConnected ((⁅K, H⁆ : Subgroup G) : Set G) := by
  let L : Subgroup G := ⁅K, H⁆
  let : ContinuousConstSMul L L :=
    Topology.IsInducing.subtypeVal.continuousConstSMul
      (Subtype.val : L → G) (fun {_ _} ↦ rfl)
  let : PreconnectedSpace H := Subtype.preconnectedSpace hH
  let C : Subgroup L := connectedComponentOfOneOfContinuousConstSMul L
  have hle : L ≤ C.map L.subtype := by
    apply commutator_le.mpr
    intro g hg h hh
    have hmaps : Set.MapsTo (fun h : G ↦ ⁅g, h⁆) (H : Set G) (L : Set G) :=
      fun h hh ↦ commutator_mem_commutator hg hh
    let f : H → L :=
      hmaps.restrict (fun h : G ↦ ⁅g, h⁆) (H : Set G) (L : Set G)
    have hf : Continuous f := (hcomm g hg).mapsToRestrict hmaps
    have hone : (1 : L) ∈ Set.range f := by
      refine ⟨(1 : H), ?_⟩
      apply Subtype.ext
      exact commutatorElement_one_right g
    have hsubset : Set.range f ⊆ (C : Set L) :=
      (isPreconnected_range hf).subset_connectedComponent hone
    have hmem : f ⟨h, hh⟩ ∈ C := hsubset ⟨⟨h, hh⟩, rfl⟩
    exact mem_map_of_mem L.subtype hmem
  have heq : C.map L.subtype = L := le_antisymm (map_subtype_le C) hle
  have hC : IsConnected (C : Set L) :=
    isConnected_connectedComponentOfOneOfContinuousConstSMul (G := L)
  have himage : IsConnected (C.map L.subtype : Set G) := by
    rw [coe_map]
    exact hC.image L.subtype continuous_subtype_val.continuousOn
  simpa only [heq] using himage

end Subgroup
