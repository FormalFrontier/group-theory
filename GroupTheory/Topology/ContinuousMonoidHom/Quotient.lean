/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.ContinuousMap.Quotient
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Pullback of continuous monoid homomorphisms along quotient maps

The compact-open homeomorphism for continuous maps restricts to the unit and multiplication
locus. Both hom spaces retain their stock topology, and the fibreconstant subtype retains
its inherited topology. No continuity of the monoid operations is required.

For an open normal subgroup, pullback from the stock quotient identifies its continuous
homomorphisms with the inherited kernel-containing subtype.
For a compact Hausdorff topological monoid target, the homomorphisms killing any open
subgroup form a compact set; normality of that subgroup is unnecessary.
For any subgroup, the kernel-containing set is closed whenever the target identity
singleton is closed, without any continuity assumptions on the operations.
-/

public section

open Set Topology

universe uG uH uK uS uM uZ

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

namespace ContinuousMonoidHom

variable {G : Type uG} {M : Type uM} [Group G] [TopologicalSpace G]
  [Monoid M] [TopologicalSpace M]

@[to_additive]
private def quotientGroupMk (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

@[to_additive]
private theorem quotientGroup_factorsThrough_iff (N : Subgroup G) [N.Normal]
    (f : G →ₜ* M) :
    Function.FactorsThrough f (quotientGroupMk N) ↔ N ≤ f.toMonoidHom.ker := by
  constructor
  · intro hf x hx
    have hxker : x ∈ (QuotientGroup.mk' N).ker :=
      (QuotientGroup.ker_mk' N).symm ▸ hx
    have hxq : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) 1 := by
      rw [map_one]
      exact MonoidHom.mem_ker.mp hxker
    exact MonoidHom.mem_ker.mpr ((hf hxq).trans (map_one f))
  · intro h x y hxy
    have hcomp := QuotientGroup.lift_comp_mk' N f.toMonoidHom h
    calc
      f x = QuotientGroup.lift N f.toMonoidHom h (quotientGroupMk N x) :=
        (DFunLike.congr_fun hcomp x).symm
      _ = QuotientGroup.lift N f.toMonoidHom h (quotientGroupMk N y) := congrArg _ hxy
      _ = f y := DFunLike.congr_fun hcomp y

/-- If the target identity singleton is closed, continuous homomorphisms whose kernel
contains a subgroup form a closed set. No openness or continuity of operations is needed. -/
@[to_additive /-- If the target zero singleton is closed, continuous additive homomorphisms
whose kernel contains an additive subgroup form a closed set. No openness or continuity of
operations is needed. -/]
theorem isClosed_setOf_le_ker (N : Subgroup G) (h1 : IsClosed ({1} : Set M)) :
    IsClosed {f : G →ₜ* M | N ≤ f.toMonoidHom.ker} := by
  have hset : {f : G →ₜ* M | N ≤ f.toMonoidHom.ker} =
      (toContinuousMap : (G →ₜ* M) → C(G, M)) ⁻¹'
        {f : C(G, M) | Set.MapsTo f (N : Set G) ({1} : Set M)} := by
    ext f
    constructor
    · intro hf x hx
      apply Set.mem_singleton_iff.mpr
      calc
        f.toContinuousMap x = f x := DFunLike.congr_fun (coe_toContinuousMap f) x
        _ = f.toMonoidHom x := (show f.toMonoidHom x = f x from
          DFunLike.congr_fun (coe_toMonoidHom f) x).symm
        _ = 1 := MonoidHom.mem_ker.mp (hf hx)
    · intro hf x hx
      apply MonoidHom.mem_ker.mpr
      calc
        f.toMonoidHom x = f x := DFunLike.congr_fun (coe_toMonoidHom f) x
        _ = f.toContinuousMap x := (show f.toContinuousMap x = f x from
          DFunLike.congr_fun (coe_toContinuousMap f) x).symm
        _ = 1 := Set.mem_singleton_iff.mp (hf hx)
  rw [hset]
  exact (ContinuousMap.isClosed_setOfPred_mapsTo h1 (N : Set G)).preimage
    (isInducing_toContinuousMap G M).continuous

variable [SeparatelyContinuousMul G]

/-- Pullback from the quotient by an open normal subgroup identifies continuous monoid
homomorphisms with the continuous homomorphisms whose kernel contains that subgroup. -/
@[to_additive
  /-- Pullback from the quotient by an open normal additive subgroup identifies continuous
  additive homomorphisms with those whose kernel contains that subgroup. -/]
noncomputable def quotientGroupPullbackHomeomorph (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) :
    ((G ⧸ N) →ₜ* M) ≃ₜ {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} := by
  letI := QuotientGroup.discreteTopology hN
  refine (quotientPullbackHomeomorph (quotientGroupMk N)
    (QuotientGroup.isQuotientMap_mk N) ?_).trans
      (Homeomorph.setCongr (Set.ext fun f ↦ quotientGroup_factorsThrough_iff N f))
  intro s hs
  obtain ⟨l, _, hl, hls⟩ := hs.finite_of_discrete.exists_subset_finite_image_eq
    (f := quotientGroupMk N) (s := Set.univ) (by
      intro x _
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      exact ⟨y, Set.mem_univ _, rfl⟩)
  exact ⟨l, hl.isCompact, hls⟩

/-- Continuous homomorphisms into a compact Hausdorff topological monoid whose kernel
contains an open subgroup form a compact set in the compact-open topology. The subgroup
need not be normal. -/
@[to_additive /-- Continuous additive homomorphisms into a compact Hausdorff topological
additive monoid whose kernel contains an open additive subgroup form a compact set in the
compact-open topology. -/]
theorem isCompact_setOf_le_ker [CompactSpace M] [T2Space M] [ContinuousMul M]
    (N : Subgroup G) (hN : IsOpen (N : Set G)) :
    IsCompact {f : G →ₜ* M | N ≤ f.toMonoidHom.ker} := by
  let K := Subgroup.normalClosure (N : Set G)
  have hK : IsOpen (K : Set G) :=
    Subgroup.isOpen_mono Subgroup.le_normalClosure hN
  let := QuotientGroup.discreteTopology hK
  have hset : {f : G →ₜ* M | K ≤ f.toMonoidHom.ker} =
      {f : G →ₜ* M | N ≤ f.toMonoidHom.ker} := by
    ext f
    exact (Subgroup.normalClosure_subset_iff
      (s := (N : Set G)) (N := f.toMonoidHom.ker)).symm
  rw [← hset]
  exact isCompact_iff_compactSpace.mpr
    (quotientGroupPullbackHomeomorph K hK).compactSpace

variable (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))

/-- Pullback is composition with the canonical quotient homomorphism. -/
@[to_additive]
theorem coe_quotientGroupPullbackHomeomorph_apply (f : (G ⧸ N) →ₜ* M) :
    (quotientGroupPullbackHomeomorph N hN f).val =
      f.comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } := by
  change (quotientPullbackHomeomorph (quotientGroupMk N) _ _ f).val =
    f.comp (quotientGroupMk N)
  exact coe_quotientPullbackHomeomorph_apply _ _ _ f

/-- Evaluation of pullback on a representative. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorph_apply_apply (f : (G ⧸ N) →ₜ* M) (x : G) :
    (quotientGroupPullbackHomeomorph N hN f).val x = f (QuotientGroup.mk x) := by
  rw [coe_quotientGroupPullbackHomeomorph_apply]
  rfl

/-- Descent evaluates to the original homomorphism on every representative. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorph_symm_apply_mk
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) (x : G) :
    (quotientGroupPullbackHomeomorph N hN).symm f (QuotientGroup.mk x) = f.val x := by
  change (quotientPullbackHomeomorph (quotientGroupMk N) _ _).symm
    ⟨f.val, (quotientGroup_factorsThrough_iff N f.val).2 f.property⟩
      (quotientGroupMk N x) = f.val x
  exact quotientPullbackHomeomorph_symm_apply_apply _ _ _ _ x

/-- A descended homomorphism is determined by composition with the canonical quotient. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorph_symm_eq_iff
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) (g : (G ⧸ N) →ₜ* M) :
    (quotientGroupPullbackHomeomorph N hN).symm f = g ↔
      f.val = g.comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } := by
  change (quotientPullbackHomeomorph (quotientGroupMk N) _ _).symm
    ⟨f.val, (quotientGroup_factorsThrough_iff N f.val).2 f.property⟩ = g ↔ _
  exact quotientPullbackHomeomorph_symm_eq_iff _ _ _ _ g

/-- A family of descended homomorphisms is continuous exactly when its pullbacks form a
continuous family in the ambient continuous monoid homomorphism space. -/
@[to_additive
  /-- A family of descended additive homomorphisms is continuous exactly when its pullbacks
  form a continuous family in the ambient continuous additive homomorphism space. -/]
theorem continuous_quotientGroupPullbackHomeomorph_symm_iff
    {Z : Type uZ} [TopologicalSpace Z]
    (F : Z → {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) :
    Continuous (fun z ↦ (quotientGroupPullbackHomeomorph N hN).symm (F z)) ↔
      Continuous (fun z ↦ (F z).val) := by
  change Continuous (fun z ↦ (quotientPullbackHomeomorph (quotientGroupMk N) _ _).symm
    ⟨(F z).val, (quotientGroup_factorsThrough_iff N (F z).val).2 (F z).property⟩) ↔ _
  exact continuous_quotientPullbackHomeomorph_symm_iff _ _ _ _

end ContinuousMonoidHom
