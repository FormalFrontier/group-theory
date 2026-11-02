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

For a normal subgroup with discrete quotient, pullback from the quotient identifies its
continuous homomorphisms with the inherited kernel-containing subtype. Descent has the
canonical quotient lift as its underlying monoid homomorphism, without continuity
assumptions on the group operations. The open-normal-subgroup construction specializes
this identification when multiplication is separately continuous.
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

section DiscreteQuotient

/-- Pullback from a discrete quotient by a normal subgroup, with inverse given by the
canonical quotient lift. No continuity of the source or target operations is required. -/
@[to_additive /-- Pullback from a discrete quotient by a normal additive subgroup, with
inverse given by the canonical quotient lift. No continuity of the operations is required. -/]
noncomputable def quotientGroupPullbackHomeomorphOfDiscrete (N : Subgroup G) [N.Normal]
    [DiscreteTopology (G ⧸ N)] :
    ((G ⧸ N) →ₜ* M) ≃ₜ {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} := by
  let q := quotientGroupMk N
  have hq : IsQuotientMap q := QuotientGroup.isQuotientMap_mk N
  have hcompact : ∀ s : Set (G ⧸ N), IsCompact s →
      ∃ l : Set G, IsCompact l ∧ Set.image q l = s := by
    intro s hs
    obtain ⟨l, _, hl, hls⟩ := hs.finite_of_discrete.exists_subset_finite_image_eq
      (f := q) (s := Set.univ) (by
        intro x _
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
        exact ⟨y, Set.mem_univ _, rfl⟩)
    exact ⟨l, hl.isCompact, hls⟩
  let E : ((G ⧸ N) →ₜ* M) ≃ₜ {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} :=
    (quotientPullbackHomeomorph q hq hcompact).trans
      (Homeomorph.setCongr (Set.ext fun f ↦ quotientGroup_factorsThrough_iff N f))
  -- Fix the function data independently of the compact-open continuity argument.
  let F : ((G ⧸ N) →ₜ* M) → {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} := fun f ↦
    ⟨f.comp q, (quotientGroup_factorsThrough_iff N _).mp (by
      intro x y hxy
      exact congrArg f hxy)⟩
  let L : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} → ((G ⧸ N) →ₜ* M) := fun f ↦
    { toMonoidHom := QuotientGroup.lift N f.val.toMonoidHom f.property
      continuous_toFun := continuous_of_discreteTopology }
  have hF (f : (G ⧸ N) →ₜ* M) : E f = F f := by
    apply Subtype.ext
    change (quotientPullbackHomeomorph q hq hcompact f).val = f.comp q
    exact coe_quotientPullbackHomeomorph_apply q hq hcompact f
  have hL (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) : E.symm f = L f := by
    apply ContinuousMonoidHom.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    change (quotientPullbackHomeomorph q hq hcompact).symm
      ⟨f.val, (quotientGroup_factorsThrough_iff N f.val).2 f.property⟩ (q g) =
        QuotientGroup.lift N f.val.toMonoidHom f.property (q g)
    rw [quotientPullbackHomeomorph_symm_apply_apply]
    exact (DFunLike.congr_fun
      (QuotientGroup.lift_comp_mk' N f.val.toMonoidHom f.property) g).symm
  exact
    { toFun := F
      invFun := L
      left_inv := by
        intro f
        apply ContinuousMonoidHom.ext
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
        exact DFunLike.congr_fun
          (QuotientGroup.lift_comp_mk' N (F f).val.toMonoidHom (F f).property) g
      right_inv := by
        intro f
        apply Subtype.ext
        apply ContinuousMonoidHom.ext
        intro x
        exact DFunLike.congr_fun
          (QuotientGroup.lift_comp_mk' N f.val.toMonoidHom f.property) x
      continuous_toFun := E.continuous.congr hF
      continuous_invFun := E.continuous_symm.congr hL }

variable (N : Subgroup G) [N.Normal] [DiscreteTopology (G ⧸ N)]

/-- Pullback is composition with the canonical quotient homomorphism. -/
@[to_additive]
theorem coe_quotientGroupPullbackHomeomorphOfDiscrete_apply (f : (G ⧸ N) →ₜ* M) :
    (quotientGroupPullbackHomeomorphOfDiscrete N f).val =
      f.comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } := by
  rfl

/-- The underlying monoid homomorphism of pullback is canonical precomposition. -/
@[to_additive]
theorem toMonoidHom_quotientGroupPullbackHomeomorphOfDiscrete_apply
    (f : (G ⧸ N) →ₜ* M) :
    (quotientGroupPullbackHomeomorphOfDiscrete N f).val.toMonoidHom =
      f.toMonoidHom.comp (QuotientGroup.mk' N) := by
  rfl

/-- Evaluation of pullback on the canonical quotient projection. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorphOfDiscrete_apply_apply
    (f : (G ⧸ N) →ₜ* M) (x : G) :
    (quotientGroupPullbackHomeomorphOfDiscrete N f).val x =
      f ((QuotientGroup.mk' N) x) := by
  rfl

/-- The underlying monoid homomorphism of descent is the canonical quotient lift. -/
@[to_additive]
theorem toMonoidHom_quotientGroupPullbackHomeomorphOfDiscrete_symm
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) :
    ((quotientGroupPullbackHomeomorphOfDiscrete N).symm f).toMonoidHom =
      QuotientGroup.lift N f.val.toMonoidHom f.property := by
  rfl

/-- Canonical descent evaluates to the original homomorphism on the quotient projection. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorphOfDiscrete_symm_apply_mk
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) (x : G) :
    (quotientGroupPullbackHomeomorphOfDiscrete N).symm f ((QuotientGroup.mk' N) x) =
      f.val x :=
  (DFunLike.congr_fun
    (toMonoidHom_quotientGroupPullbackHomeomorphOfDiscrete_symm N f) _).trans
      (QuotientGroup.lift_mk' N f.property x)

/-- Composing canonical descent with the original quotient projection recovers the map. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorphOfDiscrete_symm_comp
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) :
    ((quotientGroupPullbackHomeomorphOfDiscrete N).symm f).comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } = f.val := by
  ext x
  exact quotientGroupPullbackHomeomorphOfDiscrete_symm_apply_mk N f x

/-- The universal property of canonical continuous descent from a discrete quotient. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorphOfDiscrete_comp_eq_iff
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) (g : (G ⧸ N) →ₜ* M) :
    g.comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } = f.val ↔
      g = (quotientGroupPullbackHomeomorphOfDiscrete N).symm f := by
  constructor
  · intro h
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact (DFunLike.congr_fun h y).trans
      (quotientGroupPullbackHomeomorphOfDiscrete_symm_apply_mk N f y).symm
  · rintro rfl
    exact quotientGroupPullbackHomeomorphOfDiscrete_symm_comp N f

/-- A family of canonical descents is continuous exactly when its pullbacks form a
continuous family in the ambient continuous monoid homomorphism space. -/
@[to_additive /-- A family of canonical descents is continuous exactly when its pullbacks
form a continuous family in the ambient continuous additive monoid homomorphism space. -/]
theorem continuous_quotientGroupPullbackHomeomorphOfDiscrete_symm_iff
    {Z : Type uZ} [TopologicalSpace Z]
    (F : Z → {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) :
    Continuous (fun z ↦ (quotientGroupPullbackHomeomorphOfDiscrete N).symm (F z)) ↔
      Continuous (fun z ↦ (F z).val) := by
  constructor
  · intro hF
    simpa only [Function.comp_def, quotientGroupPullbackHomeomorphOfDiscrete_symm_comp] using
      (continuous_comp_left
        ({ toMonoidHom := QuotientGroup.mk' N
           continuous_toFun := QuotientGroup.continuous_mk } : G →ₜ* G ⧸ N)).comp hF
  · intro hF
    exact (quotientGroupPullbackHomeomorphOfDiscrete N).symm.continuous.comp
      (hF.subtype_mk fun z ↦ (F z).property)

/-- Canonical descent commutes with continuous coefficient postcomposition. -/
@[to_additive /-- Canonical descent commutes with continuous additive coefficient
postcomposition. -/]
theorem comp_quotientGroupPullbackHomeomorphOfDiscrete_symm
    {P : Type uK} [Monoid P] [TopologicalSpace P] (a : M →ₜ* P)
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) :
    a.comp ((quotientGroupPullbackHomeomorphOfDiscrete N).symm f) =
      (quotientGroupPullbackHomeomorphOfDiscrete N).symm
        ⟨a.comp f.val, by
          intro x hx
          apply MonoidHom.mem_ker.mpr
          have hf : f.val x = 1 := MonoidHom.mem_ker.mp (f.property hx)
          change a (f.val x) = 1
          rw [hf, map_one]⟩ := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  simp only [coe_comp, Function.comp_apply,
    quotientGroupPullbackHomeomorphOfDiscrete_symm_apply_mk]

end DiscreteQuotient

variable [SeparatelyContinuousMul G]

/-- Pullback from the quotient by an open normal subgroup identifies continuous monoid
homomorphisms with the continuous homomorphisms whose kernel contains that subgroup. -/
@[to_additive
  /-- Pullback from the quotient by an open normal additive subgroup identifies continuous
  additive homomorphisms with those whose kernel contains that subgroup. -/]
noncomputable def quotientGroupPullbackHomeomorph (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) :
    ((G ⧸ N) →ₜ* M) ≃ₜ {f : G →ₜ* M // N ≤ f.toMonoidHom.ker} := by
  letI := (QuotientGroup.discreteTopology_iff (N := N)).2 hN
  exact quotientGroupPullbackHomeomorphOfDiscrete N

/-- The open-subgroup construction agrees with the discrete-quotient construction. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorph_eq_of_discrete (N : Subgroup G) [N.Normal]
    [DiscreteTopology (G ⧸ N)] (hN : IsOpen (N : Set G)) :
    (quotientGroupPullbackHomeomorph N hN :
      ((G ⧸ N) →ₜ* M) ≃ₜ {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) =
        quotientGroupPullbackHomeomorphOfDiscrete N := by
  rfl

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
  let := (QuotientGroup.discreteTopology_iff (N := N)).2 hN
  exact coe_quotientGroupPullbackHomeomorphOfDiscrete_apply N f

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
  let := (QuotientGroup.discreteTopology_iff (N := N)).2 hN
  exact quotientGroupPullbackHomeomorphOfDiscrete_symm_apply_mk N f x

/-- A descended homomorphism is determined by composition with the canonical quotient. -/
@[to_additive]
theorem quotientGroupPullbackHomeomorph_symm_eq_iff
    (f : {f : G →ₜ* M // N ≤ f.toMonoidHom.ker}) (g : (G ⧸ N) →ₜ* M) :
    (quotientGroupPullbackHomeomorph N hN).symm f = g ↔
      f.val = g.comp
        { toMonoidHom := QuotientGroup.mk' N
          continuous_toFun := QuotientGroup.continuous_mk } := by
  let := (QuotientGroup.discreteTopology_iff (N := N)).2 hN
  constructor
  · rintro rfl
    exact (quotientGroupPullbackHomeomorphOfDiscrete_symm_comp N f).symm
  · intro h
    exact ((quotientGroupPullbackHomeomorphOfDiscrete_comp_eq_iff N f g).mp h.symm).symm

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
  let := (QuotientGroup.discreteTopology_iff (N := N)).2 hN
  exact continuous_quotientGroupPullbackHomeomorphOfDiscrete_symm_iff N F

end ContinuousMonoidHom
