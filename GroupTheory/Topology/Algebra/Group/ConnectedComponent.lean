/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Subgroup

/-!
# Identity components inside subgroups

Assuming only continuity of fixed left translations, the identity component of
an intermediate subgroup containing the ambient identity component maps onto
that component under the original subgroup inclusion. In particular, the
identity-component subgroup has itself as its identity component.

All subgroup groups and topologies are the canonical ones inherited from the
ambient group. No normality or separation assumptions are needed. The analogous
statements for additive groups are provided as well.
-/

@[expose] public section

universe u

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- Fixed left translations on a subgroup are continuous for its induced topology. -/
@[to_additive
/-- Fixed left translations on an additive subgroup are continuous for its induced topology. -/]
theorem continuousConstSMul_subtype (H : Subgroup G) : ContinuousConstSMul H H := by
  constructor
  intro h
  exact ((Homeomorph.smul (α := G) (h : G)).continuous.comp
    continuous_subtype_val).subtype_mk (fun x ↦ H.mul_mem h.property x.property)

attribute [local instance] continuousConstSMul_subtype AddSubgroup.continuousConstVAdd_subtype

/-- In a preconnected group, the identity-component subgroup is the whole group. -/
@[to_additive (attr := simp)
/-- In a preconnected additive group, the zero-component subgroup is the whole group. -/]
theorem connectedComponentOfOneOfContinuousConstSMul_eq_top [PreconnectedSpace G] :
    connectedComponentOfOneOfContinuousConstSMul G = ⊤ := by
  exact top_unique
    (le_connectedComponentOfOneOfContinuousConstSMul (⊤ : Subgroup G) isPreconnected_univ)

/-- The identity-component subgroup is its own identity component for its
canonical subgroup topology. -/
@[to_additive (attr := simp)
/-- The zero-component additive subgroup is its own zero component for its
canonical subgroup topology. -/]
theorem connectedComponentOfOneOfContinuousConstSMul_self :
    connectedComponentOfOneOfContinuousConstSMul
      (connectedComponentOfOneOfContinuousConstSMul G) = ⊤ := by
  let : ConnectedSpace (connectedComponentOfOneOfContinuousConstSMul G) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_connectedComponentOfOneOfContinuousConstSMul (G := G))
  exact connectedComponentOfOneOfContinuousConstSMul_eq_top

/-- If a subgroup contains the ambient identity component, its identity component
maps onto the ambient identity component under the original subgroup inclusion. -/
@[to_additive
/-- If an additive subgroup contains the ambient zero component, its zero component
maps onto the ambient zero component under the original additive subgroup inclusion. -/]
theorem map_connectedComponentOfOneOfContinuousConstSMul_subtype (H : Subgroup G)
    (h : connectedComponentOfOneOfContinuousConstSMul G ≤ H) :
    (connectedComponentOfOneOfContinuousConstSMul H).map H.subtype =
      connectedComponentOfOneOfContinuousConstSMul G := by
  refine le_antisymm
    (map_connectedComponentOfOneOfContinuousConstSMul_le H.subtype continuous_subtype_val) ?_
  let ι : connectedComponentOfOneOfContinuousConstSMul G →* H :=
    (connectedComponentOfOneOfContinuousConstSMul G).subtype.codRestrict H.toSubmonoid
      (fun x ↦ h x.property)
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  intro x hx
  have hx' : (⟨x, hx⟩ : connectedComponentOfOneOfContinuousConstSMul G) ∈
      connectedComponentOfOneOfContinuousConstSMul
        (connectedComponentOfOneOfContinuousConstSMul G) := by
    rw [connectedComponentOfOneOfContinuousConstSMul_self]
    trivial
  let y := ι.connectedComponentOfOneMap hι ⟨⟨x, hx⟩, hx'⟩
  exact ⟨(y : H), y.property,
    congrArg (fun z : H ↦ (z : G))
      (MonoidHom.connectedComponentOfOneMap_apply ι hι ⟨⟨x, hx⟩, hx'⟩)⟩

/-!
## Open subgroups

An open subgroup contains the identity component. If the component space is finite,
every open subgroup has finite index, still assuming only continuity of fixed left
translations.
-/

open scoped Pointwise

/-- An open subgroup contains the identity-component subgroup when fixed left
translations are continuous. -/
@[to_additive
/-- An open additive subgroup contains the zero-component subgroup when fixed left
translations are continuous. -/]
theorem connectedComponentOfOneOfContinuousConstSMul_le_of_isOpen
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    connectedComponentOfOneOfContinuousConstSMul G ≤ H := by
  have hopen : IsOpen (H : Set G)ᶜ := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro g hg
    refine ⟨g • (H : Set G), ?_, IsOpen.smul hH g, ?_⟩
    · rintro y ⟨h, hh, rfl⟩ hy
      apply hg
      change g ∈ H
      simpa only [smul_eq_mul, mul_inv_cancel_right] using H.mul_mem hy (H.inv_mem hh)
    · exact ⟨1, H.one_mem, by simp only [smul_eq_mul, mul_one]⟩
  have hclopen : IsClopen (H : Set G) := ⟨isOpen_compl_iff.mp hopen, hH⟩
  intro x hx
  exact IsClopen.connectedComponent_subset hclopen H.one_mem
    ((mem_connectedComponentOfOneOfContinuousConstSMul x).mp hx)

/-- In a group with finitely many connected components, every open subgroup has
finite index, assuming only continuity of fixed left translations. -/
@[to_additive
/-- In an additive group with finitely many connected components, every open
additive subgroup has finite index, assuming only continuity of fixed left translations. -/]
theorem finiteIndex_of_isOpen_of_finite_connectedComponents
    [Finite (ConnectedComponents G)] (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    H.FiniteIndex := by
  have : (connectedComponentOfOneOfContinuousConstSMul G).FiniteIndex :=
    finiteIndex_connectedComponentOfOneOfContinuousConstSMul
  exact finiteIndex_of_le (connectedComponentOfOneOfContinuousConstSMul_le_of_isOpen H hH)

open Topology

/-- When open subgroups form a neighborhood basis at the identity, their infimum
has carrier equal to the closure of the identity singleton. -/
@[to_additive
/-- When open additive subgroups form a neighborhood basis at zero, their infimum
has carrier equal to the closure of the zero singleton. -/]
theorem coe_iInf_openSubgroup_eq_closure_one
    (hB : (nhds (1 : G)).HasBasis (fun _ : OpenSubgroup G => True)
      (fun H => (H : Set G))) :
    ((⨅ H : OpenSubgroup G, H.toSubgroup : Subgroup G) : Set G) =
      _root_.closure ({1} : Set G) := by
  ext x
  change x ∈ (⨅ H : OpenSubgroup G, H.toSubgroup : Subgroup G) ↔
    x ∈ _root_.closure ({1} : Set G)
  rw [Subgroup.mem_iInf]
  constructor
  · intro hx
    rw [mem_closure_iff]
    intro U hU hxU
    have hleft : Continuous (fun y : G ↦ x * y) := continuous_const_smul x
    have hV : {y : G | x * y ∈ U} ∈ nhds (1 : G) :=
      (hU.preimage hleft).mem_nhds (by
        simpa only [Set.mem_preimage, mul_one] using hxU)
    obtain ⟨H, _, hH⟩ := hB.mem_iff.mp hV
    have h1 : x * x⁻¹ ∈ U := hH (H.inv_mem (hx H))
    exact ⟨1, by simpa only [mul_inv_cancel] using h1, rfl⟩
  · intro hx H
    have hleft : Continuous (fun y : G ↦ x⁻¹ * y) := continuous_const_smul x⁻¹
    have hopen : IsOpen {y : G | x⁻¹ * y ∈ H.toSubgroup} := H.isOpen.preimage hleft
    have hxmem : x ∈ {y : G | x⁻¹ * y ∈ H.toSubgroup} := by
      simpa only [Set.mem_ofPred_eq, inv_mul_cancel] using H.toSubgroup.one_mem
    obtain ⟨y, hy, hy1⟩ := mem_closure_iff.mp hx _ hopen hxmem
    have hy_eq : y = 1 := Set.mem_singleton_iff.mp hy1
    have hinv : x⁻¹ ∈ H.toSubgroup := by
      simpa only [Set.mem_ofPred_eq, hy_eq, mul_one] using hy
    simpa only [inv_inv] using H.toSubgroup.inv_mem hinv

end Subgroup

namespace MonoidHom

universe v w

variable {G : Type u} {H : Type v} {K : Type w}
  [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [Group H] [TopologicalSpace H] [ContinuousConstSMul H H]
  [Group K] [TopologicalSpace K] [ContinuousConstSMul K K]

/-- Restricting the identity homomorphism to the identity component gives the identity. -/
@[to_additive (attr := simp)
/-- Restricting the identity homomorphism to the zero component gives the identity. -/]
theorem connectedComponentOfOneMap_id :
    (MonoidHom.id G).connectedComponentOfOneMap continuous_id =
      MonoidHom.id (Subgroup.connectedComponentOfOneOfContinuousConstSMul G) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact connectedComponentOfOneMap_apply (MonoidHom.id G) continuous_id x

/-- Restriction to identity components preserves composition of continuous homomorphisms. -/
@[to_additive (attr := simp)
/-- Restriction to zero components preserves composition of continuous homomorphisms. -/]
theorem connectedComponentOfOneMap_comp (f : G →* H) (g : H →* K)
    (hf : Continuous f) (hg : Continuous g) :
    (g.comp f).connectedComponentOfOneMap (hg.comp hf) =
      (g.connectedComponentOfOneMap hg).comp (f.connectedComponentOfOneMap hf) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change ((g.comp f).connectedComponentOfOneMap (hg.comp hf) x : K) =
    (g.connectedComponentOfOneMap hg (f.connectedComponentOfOneMap hf x) : K)
  simp only [connectedComponentOfOneMap_apply, MonoidHom.comp_apply]

end MonoidHom
