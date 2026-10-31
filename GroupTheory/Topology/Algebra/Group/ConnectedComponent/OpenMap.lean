/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.ConnectedComponent

/-!
# Identity components under open homomorphisms

A continuous open group homomorphism with preconnected kernel pulls the identity
component back to the identity component. Its restriction to identity components
is surjective, even when the original homomorphism is not surjective.

Only continuity of fixed left translations is assumed. The proof uses the
canonical induced topology on the range, whose identity component maps onto the
ambient identity component because the range is an open subgroup.

The corresponding statements for additive groups are provided as well.
-/

@[expose] public section

universe u v

namespace MonoidHom

variable {G : Type u} {H : Type v}
  [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [Group H] [TopologicalSpace H] [ContinuousConstSMul H H]

/-- The preimage of the identity-component subgroup under a continuous open
homomorphism with preconnected kernel is the identity-component subgroup. -/
@[to_additive
/-- The preimage of the zero-component subgroup under a continuous open additive
homomorphism with preconnected kernel is the zero-component subgroup. -/]
theorem comap_connectedComponentOfOneOfContinuousConstSMul_eq (q : G →* H)
    (hq : Continuous q) (ho : IsOpenMap q) (hk : IsPreconnected (q.ker : Set G)) :
    (Subgroup.connectedComponentOfOneOfContinuousConstSMul H).comap q =
      Subgroup.connectedComponentOfOneOfContinuousConstSMul G := by
  let : ContinuousConstSMul q.range q.range :=
    Subgroup.continuousConstSMul_subtype q.range
  have hR : IsOpen (q.range : Set H) := by
    change IsOpen (Set.range q)
    simpa only [Set.image_univ] using ho (Set.univ : Set G) isOpen_univ
  have hKH :=
    Subgroup.connectedComponentOfOneOfContinuousConstSMul_le_of_isOpen q.range hR
  have hmap :=
    Subgroup.map_connectedComponentOfOneOfContinuousConstSMul_subtype q.range hKH
  have hcont : Continuous q.rangeRestrict := hq.subtype_mk _
  have hopen : IsOpenMap q.rangeRestrict := by
    apply IsOpenMap.subtype_mk
    exact ho
  have hsurj : Function.Surjective q.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hfib : ∀ y : q.range, IsPreconnected (q.rangeRestrict ⁻¹' {y}) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have hfiber : q.rangeRestrict ⁻¹' {q.rangeRestrict x} =
        (fun k : G ↦ x * k) '' (q.ker : Set G) := by
      ext z
      constructor
      · intro hz
        have hqz : q z = q x :=
          congrArg (fun t : q.range ↦ (t : H)) (Set.mem_singleton_iff.mp hz)
        refine ⟨x⁻¹ * z, ?_, by simp only [mul_inv_cancel_left]⟩
        change q (x⁻¹ * z) = 1
        simp only [map_mul, map_inv, hqz, inv_mul_cancel]
      · rintro ⟨k, hk, rfl⟩
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        change q (x * k) = q x
        change q k = 1 at hk
        simp only [map_mul, hk, mul_one]
    rw [hfiber]
    have hleft : Continuous (fun k : G ↦ x * k) := continuous_const_smul x
    exact hk.image (fun k : G ↦ x * k) hleft.continuousOn
  have hKr :=
    (Subgroup.isConnected_connectedComponentOfOneOfContinuousConstSMul
      (G := q.range)).isPreconnected
  have hpre : IsPreconnected
      ((Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range).comap
        q.rangeRestrict : Set G) := by
    change IsPreconnected (q.rangeRestrict ⁻¹'
      (Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range))
    -- The open cover meets a common fiber over the component; that fiber then
    -- supplies a point in both members of the cover.
    intro U V hU hV hcover hUne hVne
    have hcover' :
        (Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range) ⊆
          q.rangeRestrict '' U ∪ q.rangeRestrict '' V := by
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      rcases hcover hy with hxU | hxV
      · exact Or.inl ⟨x, hxU, rfl⟩
      · exact Or.inr ⟨x, hxV, rfl⟩
    have hUne' :
        ((Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range) ∩
          q.rangeRestrict '' U).Nonempty := by
      obtain ⟨x, hxC, hxU⟩ := hUne
      exact ⟨q.rangeRestrict x, hxC, x, hxU, rfl⟩
    have hVne' :
        ((Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range) ∩
          q.rangeRestrict '' V).Nonempty := by
      obtain ⟨x, hxC, hxV⟩ := hVne
      exact ⟨q.rangeRestrict x, hxC, x, hxV, rfl⟩
    obtain ⟨y, hyC, hyU, hyV⟩ :=
      hKr (q.rangeRestrict '' U) (q.rangeRestrict '' V)
        (hopen U hU) (hopen V hV) hcover' hUne' hVne'
    have hFcover : q.rangeRestrict ⁻¹' {y} ⊆ U ∪ V := by
      intro x hx
      apply hcover
      change q.rangeRestrict x ∈
        (Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range)
      rw [Set.mem_singleton_iff.mp hx]
      exact hyC
    have hFUne : (q.rangeRestrict ⁻¹' {y} ∩ U).Nonempty := by
      obtain ⟨x, hxU, hxy⟩ := hyU
      exact ⟨x, Set.mem_singleton_iff.mpr hxy, hxU⟩
    have hFVne : (q.rangeRestrict ⁻¹' {y} ∩ V).Nonempty := by
      obtain ⟨x, hxV, hxy⟩ := hyV
      exact ⟨x, Set.mem_singleton_iff.mpr hxy, hxV⟩
    obtain ⟨x, hxF, hxU, hxV⟩ := (hfib y) U V hU hV hFcover hFUne hFVne
    refine ⟨x, ?_, hxU, hxV⟩
    change q.rangeRestrict x ∈
      (Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range : Set q.range)
    rw [Set.mem_singleton_iff.mp hxF]
    exact hyC
  have hcomap :
      (Subgroup.connectedComponentOfOneOfContinuousConstSMul H).comap q =
        (Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range).comap
          q.rangeRestrict := by
    ext x
    change q x ∈ Subgroup.connectedComponentOfOneOfContinuousConstSMul H ↔
      q.rangeRestrict x ∈ Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range
    rw [← hmap]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hy' : y = q.rangeRestrict x := Subtype.ext hyx
      exact hy' ▸ hy
    · intro hx
      exact ⟨q.rangeRestrict x, hx, rfl⟩
  rw [hcomap]
  refine le_antisymm
    (Subgroup.le_connectedComponentOfOneOfContinuousConstSMul _ hpre) ?_
  intro x hx
  change q.rangeRestrict x ∈ Subgroup.connectedComponentOfOneOfContinuousConstSMul q.range
  exact (Subgroup.map_connectedComponentOfOneOfContinuousConstSMul_le
    q.rangeRestrict hcont) ⟨x, hx, rfl⟩

/-- A continuous open homomorphism with preconnected kernel induces a surjection
on identity components; the homomorphism itself need not be surjective. -/
@[to_additive
/-- A continuous open additive homomorphism with preconnected kernel induces a
surjection on zero components; the homomorphism itself need not be surjective. -/]
theorem connectedComponentOfOneMap_surjective_of_isOpenMap (q : G →* H)
    (hq : Continuous q) (ho : IsOpenMap q) (hk : IsPreconnected (q.ker : Set G)) :
    Function.Surjective (q.connectedComponentOfOneMap hq) := by
  have hR : IsOpen (q.range : Set H) := by
    change IsOpen (Set.range q)
    simpa only [Set.image_univ] using ho (Set.univ : Set G) isOpen_univ
  have hKH :=
    Subgroup.connectedComponentOfOneOfContinuousConstSMul_le_of_isOpen q.range hR
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hKH hy
  have hxK : x ∈ Subgroup.connectedComponentOfOneOfContinuousConstSMul G := by
    rw [← q.comap_connectedComponentOfOneOfContinuousConstSMul_eq hq ho hk]
    change q x ∈ Subgroup.connectedComponentOfOneOfContinuousConstSMul H
    rw [hx]
    exact hy
  refine ⟨⟨x, hxK⟩, ?_⟩
  apply Subtype.ext
  change (q.connectedComponentOfOneMap hq ⟨x, hxK⟩ : H) = y
  rw [connectedComponentOfOneMap_apply]
  exact hx

end MonoidHom
