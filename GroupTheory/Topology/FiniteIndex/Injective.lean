/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.AutomaticContinuity
public import Mathlib.GroupTheory.Index

/-!
# Open finite-index subgroups and injective continuous homomorphisms

If every finite-index subgroup of a group is open, the same holds for a group admitting
a continuous injective homomorphism into it with finite-index range.

The proof applies `Subgroup.isOpen_finiteIndex_of_finiteIndex` to the range with its
inherited topology, then pulls open subgroups back along the range restriction.
The topology on the source need not agree with the topology induced from the range,
and no continuity of the group operations is required.
-/

@[expose] public section

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- A continuous injective group homomorphism with finite-index range pulls back the
openness of all finite-index subgroups from its codomain to its domain.

No continuity assumption on the group operations is needed, and the homomorphism need
not be a topological embedding. -/
@[to_additive /-- A continuous injective additive group homomorphism with finite-index
range pulls back the openness of all finite-index additive subgroups from its codomain
to its domain.

No continuity assumption on the additive group operations is needed, and the
homomorphism need not be a topological embedding. -/]
theorem MonoidHom.isOpen_finiteIndex_of_continuous_injective
    (f : G →* H) (hf : Continuous f) (hinj : Function.Injective f)
    [f.range.FiniteIndex]
    (hH : ∀ L : Subgroup H, L.FiniteIndex → IsOpen (L : Set H)) :
    ∀ K : Subgroup G, K.FiniteIndex → IsOpen (K : Set G) := by
  have hHRange :
      ∀ L : Subgroup f.range, L.FiniteIndex → IsOpen (L : Set f.range) :=
    Subgroup.isOpen_finiteIndex_of_finiteIndex f.range hH
  have hfRange : Continuous f.rangeRestrict :=
    hf.subtype_mk (fun x => ⟨x, rfl⟩)
  have hinjRange : Function.Injective f.rangeRestrict := by
    intro x y h
    exact hinj (congrArg Subtype.val h)
  intro K hK
  have : K.FiniteIndex := hK
  have hrel : K.IsFiniteRelIndex (⊤ : Subgroup G) :=
    Subgroup.isFiniteRelIndex_top_iff.mpr inferInstance
  have hmap : (K.map f.rangeRestrict).IsFiniteRelIndex
      ((⊤ : Subgroup G).map f.rangeRestrict) :=
    Subgroup.IsFiniteRelIndex.map f.rangeRestrict hrel
  have htop : (⊤ : Subgroup G).map f.rangeRestrict = ⊤ :=
    Subgroup.map_top_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  rw [htop] at hmap
  have hKmap : (K.map f.rangeRestrict).FiniteIndex :=
    Subgroup.isFiniteRelIndex_top_iff.mp hmap
  have hKopen : IsOpen ((K.map f.rangeRestrict : Subgroup f.range) : Set f.range) :=
    hHRange (K.map f.rangeRestrict) hKmap
  simpa only [Subgroup.coe_map, Set.preimage_image_eq (K : Set G) hinjRange] using
    hKopen.preimage hfRange
