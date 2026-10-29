/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.ContinuousMap.Quotient
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Pullback of continuous monoid homomorphisms along quotient maps

The compact-open homeomorphism for continuous maps restricts to the unit and multiplication
locus. Both hom spaces retain their stock topology, and the fibreconstant subtype retains
its inherited topology. No continuity of the monoid operations is required.
-/

public section

open Set Topology

universe uG uH uK uS

namespace ContinuousMonoidHom

variable {G : Type uG} {H : Type uH} {K : Type uK}
  [Monoid G] [Monoid H] [Monoid K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]

@[to_additive]
private theorem range_comp_iff (q : G →ₜ* H) (hq : Function.Surjective q)
    (f : C(H, K)) :
    f ∈ Set.range (toContinuousMap : (H →ₜ* K) → C(H, K)) ↔
      f.comp q.toContinuousMap ∈ Set.range (toContinuousMap : (G →ₜ* K) → C(G, K)) := by
  rw [range_toContinuousMap, range_toContinuousMap]
  constructor
  · rintro ⟨h1, hm⟩
    exact ⟨by simpa only [ContinuousMap.comp_apply, coe_toContinuousMap,
        ContinuousMap.coe_apply, map_one] using h1,
      fun x y ↦ by
        simpa only [ContinuousMap.comp_apply, coe_toContinuousMap,
          ContinuousMap.coe_apply, map_mul] using hm (q x) (q y)⟩
  · rintro ⟨h1, hm⟩
    refine ⟨by simpa only [ContinuousMap.comp_apply, coe_toContinuousMap,
        ContinuousMap.coe_apply, map_one] using h1, ?_⟩
    intro x y
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    simpa only [ContinuousMap.comp_apply, coe_toContinuousMap,
      ContinuousMap.coe_apply, map_mul] using hm a b

@[to_additive]
private noncomputable def fibreMapHomeomorph (q : G →ₜ* H) :
    {g : G →ₜ* K // Function.FactorsThrough g q} ≃ₜ
      {g : {g : C(G, K) // Function.FactorsThrough g q} //
        g.val ∈ Set.range (toContinuousMap : (G →ₜ* K) → C(G, K))} := by
  let j : {g : G →ₜ* K // Function.FactorsThrough g q} →
      {g : C(G, K) // Function.FactorsThrough g q} :=
    fun g ↦ ⟨g.val.toContinuousMap, g.property⟩
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.of_comp_iff.mp
    ((isEmbedding_toContinuousMap G K).comp .subtypeVal)
  refine hj.toHomeomorph.trans (Homeomorph.setCongr ?_)
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, rfl⟩
  · rintro ⟨f, hf⟩
    have h : Function.FactorsThrough f q := by
      change Function.FactorsThrough f.toContinuousMap q
      rw [hf]
      exact g.property
    exact ⟨⟨f, h⟩, Subtype.ext hf⟩

@[to_additive]
private noncomputable def pullbackRangeHomeomorph (q : G →ₜ* H) (hq : IsQuotientMap q)
    (hcompact : ∀ s : Set H, IsCompact s →
      ∃ l : Set G, IsCompact l ∧ Set.image q l = s) :
    Set.range (toContinuousMap : (H →ₜ* K) → C(H, K)) ≃ₜ
      {g : {g : C(G, K) // Function.FactorsThrough g q} //
        g.val ∈ Set.range (toContinuousMap : (G →ₜ* K) → C(G, K))} :=
  (ContinuousMap.quotientPullbackHomeomorph q.toContinuousMap hq hcompact).subtype
    (range_comp_iff q hq.surjective)

/-- Pullback along a compact-covering quotient map on the original continuous monoid hom
spaces, with the inherited topology on fibreconstant homomorphisms. -/
@[to_additive /-- Pullback along a compact-covering quotient map on the original continuous
additive monoid hom spaces, with the inherited topology on fibreconstant homomorphisms. -/]
noncomputable def quotientPullbackHomeomorph (q : G →ₜ* H) (hq : IsQuotientMap q)
    (hcompact : ∀ s : Set H, IsCompact s →
      ∃ l : Set G, IsCompact l ∧ Set.image q l = s) :
    (H →ₜ* K) ≃ₜ {g : G →ₜ* K // Function.FactorsThrough g q} :=
  ((isEmbedding_toContinuousMap H K).toHomeomorph.trans
    (pullbackRangeHomeomorph q hq hcompact)).trans (fibreMapHomeomorph q).symm

variable (q : G →ₜ* H) (hq : IsQuotientMap q)
  (hcompact : ∀ s : Set H, IsCompact s →
    ∃ l : Set G, IsCompact l ∧ Set.image q l = s)

/-- Forgetting algebraic structure commutes with the continuous-map pullback homeomorphism. -/
@[to_additive]
theorem toContinuousMap_quotientPullbackHomeomorph_apply (f : H →ₜ* K) :
    (quotientPullbackHomeomorph q hq hcompact f).val.toContinuousMap =
      (ContinuousMap.quotientPullbackHomeomorph q.toContinuousMap hq hcompact
        f.toContinuousMap).val :=
  congrArg (fun g ↦ g.val.val) ((fibreMapHomeomorph q).apply_symm_apply
    (pullbackRangeHomeomorph q hq hcompact
      ((isEmbedding_toContinuousMap H K).toHomeomorph f)))

@[to_additive (attr := simp)]
theorem coe_quotientPullbackHomeomorph_apply (f : H →ₜ* K) :
    (quotientPullbackHomeomorph q hq hcompact f).val = f.comp q :=
  toContinuousMap_injective (toContinuousMap_quotientPullbackHomeomorph_apply q hq hcompact f)

@[to_additive]
theorem quotientPullbackHomeomorph_apply_apply (f : H →ₜ* K) (x : G) :
    (quotientPullbackHomeomorph q hq hcompact f).val x = f (q x) := by
  rw [coe_quotientPullbackHomeomorph_apply]
  rfl

@[to_additive (attr := simp)]
theorem quotientPullbackHomeomorph_symm_comp
    (g : {g : G →ₜ* K // Function.FactorsThrough g q}) :
    ((quotientPullbackHomeomorph q hq hcompact).symm g).comp q = g.val := by
  simpa only [coe_quotientPullbackHomeomorph_apply] using
    congrArg Subtype.val ((quotientPullbackHomeomorph q hq hcompact).apply_symm_apply g)

@[to_additive (attr := simp)]
theorem quotientPullbackHomeomorph_symm_apply_apply
    (g : {g : G →ₜ* K // Function.FactorsThrough g q}) (x : G) :
    (quotientPullbackHomeomorph q hq hcompact).symm g (q x) = g.val x :=
  DFunLike.congr_fun (quotientPullbackHomeomorph_symm_comp q hq hcompact g) x

/-- Descent is uniquely determined by its composite with the quotient map. -/
@[to_additive /-- Descent is uniquely determined by its composite with the quotient map. -/]
theorem quotientPullbackHomeomorph_symm_eq_iff
    (g : {g : G →ₜ* K // Function.FactorsThrough g q}) (f : H →ₜ* K) :
    (quotientPullbackHomeomorph q hq hcompact).symm g = f ↔ g.val = f.comp q := by
  constructor
  · rintro rfl
    exact (quotientPullbackHomeomorph_symm_comp q hq hcompact g).symm
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := hq.surjective y
    exact (quotientPullbackHomeomorph_symm_apply_apply q hq hcompact g x).trans
      (DFunLike.congr_fun h x)

/-- Continuity of a descended family is equivalent to continuity in the original ambient
hom space, not merely pointwise continuity. -/
@[to_additive /-- Continuity of a descended family is equivalent to continuity in the original
ambient additive hom space, not merely pointwise continuity. -/]
theorem continuous_quotientPullbackHomeomorph_symm_iff
    {S : Type uS} [TopologicalSpace S]
    (F : S → {g : G →ₜ* K // Function.FactorsThrough g q}) :
    Continuous (fun s ↦ (quotientPullbackHomeomorph q hq hcompact).symm (F s)) ↔
      Continuous (fun s ↦ (F s).val) := by
  constructor
  · intro hF
    simpa only [Function.comp_def, quotientPullbackHomeomorph_symm_comp] using
      (continuous_comp_left q).comp hF
  · intro hF
    exact (quotientPullbackHomeomorph q hq hcompact).symm.continuous.comp
      (hF.subtype_mk fun s ↦ (F s).property)

end ContinuousMonoidHom
