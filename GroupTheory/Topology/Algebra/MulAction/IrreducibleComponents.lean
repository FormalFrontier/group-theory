/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.NoetherianSpace

/-!
# Finite irreducible components and pretransitive actions

A topological space with finitely many irreducible components is locally connected and has
finitely many connected components. These conclusions do not require the irreducible components
to be disjoint, a group action, or compactness. The clopenness of connected components then
follows from Mathlib's `isClopen_connectedComponent`.

If the space also carries a pretransitive group action with continuous translations, its
irreducible components are pairwise disjoint and clopen, and coincide with its connected
components. No topology on the acting group is required, and the space may be empty.

For a Noetherian space, the finiteness hypothesis is supplied by
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.

The results use Mathlib's irreducible-component and connected-component APIs, with translation
homeomorphisms providing the action-specific component structure.
-/

@[expose] public section

universe u v

namespace TopologicalSpace

variable {X : Type v} [TopologicalSpace X]

/-- A topological space with finitely many irreducible components is locally connected, even when
its irreducible components intersect. -/
theorem locallyConnectedSpace_of_finite_irreducibleComponents
    (hfin : (irreducibleComponents X).Finite) : LocallyConnectedSpace X := by
  classical
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x U hU => ?_
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  -- Remove the components not containing the base point from an open neighborhood.
  let bad : Set (Set X) := {C ∈ irreducibleComponents X | x ∉ C}
  have hbad : bad.Finite := hfin.subset fun C hC => hC.1
  have hclosed : IsClosed (⋃₀ bad) := by
    rw [Set.sUnion_eq_biUnion]
    exact hbad.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  let V : Set X := W \ ⋃₀ bad
  have hV : IsOpen V := hW.sdiff hclosed
  have hxV : x ∈ V := by
    refine ⟨hxW, ?_⟩
    rintro ⟨C, hC, hxC⟩
    exact hC.2 hxC
  refine ⟨V, fun y hy => hWU hy.1, hV, hxV, ⟨⟨x, hxV⟩, ?_⟩⟩
  refine isPreconnected_of_forall x fun y hy => ?_
  let C : Set X := irreducibleComponent y
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents y
  have hyC : y ∈ C := mem_irreducibleComponent
  have hxC : x ∈ C := by
    by_contra hxC
    exact hy.2 (Set.mem_sUnion_of_mem hyC ⟨hC, hxC⟩)
  -- Each point is joined to the base point inside an open part of one component.
  refine ⟨V ∩ C, Set.inter_subset_left, ⟨hxV, hxC⟩, ⟨hy, hyC⟩, ?_⟩
  have hpre : IsPreirreducible ((Subtype.val : V → X) ⁻¹' C) :=
    hC.1.isPreirreducible.preimage hV.isOpenEmbedding_subtypeVal
  simpa only [Subtype.image_preimage_coe] using
    (hpre.image (Subtype.val : V → X) continuous_subtype_val.continuousOn).isPreconnected

/-- A topological space with finitely many irreducible components has finitely many connected
components, without a compactness assumption. -/
theorem finite_connectedComponents_of_finite_irreducibleComponents
    (hfin : (irreducibleComponents X).Finite) : Finite (ConnectedComponents X) := by
  classical
  let : Finite (irreducibleComponents X) := hfin.to_subtype
  let p : irreducibleComponents X → X := fun C => C.property.1.nonempty.some
  have hp (C : irreducibleComponents X) : p C ∈ (C : Set X) :=
    C.property.1.nonempty.some_mem
  refine Finite.of_surjective (fun C : irreducibleComponents X =>
    (p C : ConnectedComponents X)) ?_
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨C, ConnectedComponents.coe_eq_coe'.2 ?_⟩
  exact C.property.1.isConnected.subset_connectedComponent
    (show x ∈ (C : Set X) from mem_irreducibleComponent) (hp C)

end TopologicalSpace

namespace MulAction.IsPretransitive

variable (G : Type u) {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]
  [MulAction.IsPretransitive G X] [ContinuousConstSMul G X]

include G

/-- The irreducible components of a space with a pretransitive action and continuous translations
are pairwise disjoint if there are only finitely many of them. -/
@[to_additive /-- The irreducible components of a space with a pretransitive action and continuous
translations are pairwise disjoint if there are only finitely many of them. -/]
theorem pairwise_disjoint_irreducibleComponents (hfin : (irreducibleComponents X).Finite) :
    (irreducibleComponents X).Pairwise Disjoint := by
  classical
  intro Z hZ W hW hZW
  apply Set.disjoint_left.mpr
  intro x hxZ hxW
  -- The complement of the other components has closure `Z`, so it contains a point.
  obtain ⟨p, hp⟩ : ((⋃₀ (irreducibleComponents X \ {Z}))ᶜ).Nonempty := by
    apply closure_nonempty_iff.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z hZ]
    exact hZ.1.nonempty
  have hunique (D : Set X) (hD : D ∈ irreducibleComponents X) (hpD : p ∈ D) :
      D = Z := by
    by_contra hDZ
    apply hp
    exact Set.mem_sUnion.mpr
      ⟨D, ⟨hD, by simpa only [Set.mem_singleton_iff] using hDZ⟩, hpD⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G p x
  let e : X ≃ₜ X := Homeomorph.smul g
  -- Pull back whole maximal components, without choosing a component equivariantly.
  have hpre (D : Set X) (hD : D ∈ irreducibleComponents X) (hxD : x ∈ D) :
      e ⁻¹' D = Z := by
    apply hunique
    · exact preimage_mem_irreducibleComponents hD e.isOpenEmbedding
        ⟨x, hxD, e.surjective x⟩
    · change g • p ∈ D
      rwa [hg]
  have heq : e ⁻¹' Z = e ⁻¹' W := (hpre Z hZ hxZ).trans (hpre W hW hxW).symm
  apply hZW
  ext y
  have hy := Set.ext_iff.mp heq (e.symm y)
  simpa only [Set.mem_preimage, e.apply_symm_apply] using hy

/-- Every irreducible component of a space with a pretransitive action and continuous translations
is clopen if there are only finitely many irreducible components. -/
@[to_additive /-- Every irreducible component of a space with a pretransitive action and continuous
translations is clopen if there are only finitely many irreducible components. -/]
theorem isClopen_of_mem_irreducibleComponents (hfin : (irreducibleComponents X).Finite)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z := by
  classical
  refine ⟨isClosed_of_mem_irreducibleComponents Z hZ, ?_⟩
  have hcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_sUnion.mpr
        ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
          mem_irreducibleComponent⟩
      simpa only [Set.mem_singleton_iff] using
        (show irreducibleComponent x ≠ Z from fun h => hx (h ▸ mem_irreducibleComponent))
    · intro hx
      obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hx
      exact (pairwise_disjoint_irreducibleComponents G hfin hD.1 hZ
        (by simpa only [Set.mem_singleton_iff] using hD.2)).notMem_of_mem_left hxD
  apply isClosed_compl_iff.mp
  rw [hcompl]
  exact hfin.sdiff.isClosed_sUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1

/-- In a space with a pretransitive action, continuous translations, and finitely many irreducible
components, the connected component of a point equals its irreducible component. -/
@[to_additive /-- In a space with a pretransitive action, continuous translations, and finitely many
irreducible components, the connected component of a point equals its irreducible component. -/]
theorem connectedComponent_eq_irreducibleComponent (hfin : (irreducibleComponents X).Finite)
    (x : X) : connectedComponent x = irreducibleComponent x := by
  apply Set.Subset.antisymm
  · exact (isClopen_of_mem_irreducibleComponents G hfin
      (irreducibleComponent_mem_irreducibleComponents x)).connectedComponent_subset
        mem_irreducibleComponent
  · exact irreducibleComponent_subset_connectedComponent

/-- Every connected component of a space with a pretransitive action, continuous translations,
and finitely many irreducible components is irreducible. -/
@[to_additive /-- Every connected component of a space with a pretransitive action, continuous
translations, and finitely many irreducible components is irreducible. -/]
theorem isIrreducible_connectedComponent (hfin : (irreducibleComponents X).Finite) (x : X) :
    IsIrreducible (connectedComponent x) := by
  rw [connectedComponent_eq_irreducibleComponent G hfin x]
  exact isIrreducible_irreducibleComponent

end MulAction.IsPretransitive
