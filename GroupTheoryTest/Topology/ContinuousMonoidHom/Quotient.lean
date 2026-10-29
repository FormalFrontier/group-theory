/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.ContinuousMonoidHom.Quotient
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic.NormNum

/-! The real first projection has a continuous zero section. Its compact lifts are section
images, so compactness of the source or quotient is unnecessary. The inverse below descends
arbitrary fibreconstant original continuous additive homomorphisms. The horizontal subgroup
of the reals times the integers also gives a nonzero proper compact kernel-constrained
space with additive circle target, without compactness of the source or subgroup. -/

@[expose] public section

open Set Topology

namespace ContinuousAddMonoidHom

private def realFirstProjection : (ℝ × ℝ) →ₜ+ ℝ := fst ℝ ℝ

private def realZeroSection : C(ℝ, ℝ × ℝ) :=
  ⟨fun r ↦ (r, 0), continuous_id.prodMk continuous_const⟩

private theorem realSection_rightInverse :
    Function.RightInverse realZeroSection realFirstProjection := fun _ ↦ rfl

private theorem realProjection_isQuotientMap : IsQuotientMap realFirstProjection :=
  IsQuotientMap.of_inverse (map_continuous realZeroSection)
    (map_continuous realFirstProjection) realSection_rightInverse

private theorem realProjection_compactLift (s : Set ℝ) (hs : IsCompact s) :
    ∃ l : Set (ℝ × ℝ), IsCompact l ∧ Set.image realFirstProjection l = s := by
  refine ⟨realZeroSection '' s, hs.image (map_continuous realZeroSection), ?_⟩
  rw [← Set.image_comp, realSection_rightInverse.comp_eq_id, Set.image_id]

/-- Pullback on original additive hom spaces for the noncompact real first projection. -/
private noncomputable def realProjectionPullback :
    (ℝ →ₜ+ ℝ) ≃ₜ
      {g : (ℝ × ℝ) →ₜ+ ℝ // Function.FactorsThrough g realFirstProjection} :=
  quotientPullbackHomeomorph realFirstProjection realProjection_isQuotientMap
    realProjection_compactLift

example : NoncompactSpace ℝ := inferInstance

example (g : {g : (ℝ × ℝ) →ₜ+ ℝ // Function.FactorsThrough g realFirstProjection})
    (r : ℝ) : realProjectionPullback.symm g r = g.val (r, 0) := by
  change realProjectionPullback.symm g (realFirstProjection (r, 0)) = g.val (r, 0)
  exact quotientPullbackHomeomorph_symm_apply_apply realFirstProjection
    realProjection_isQuotientMap realProjection_compactLift g (r, 0)

end ContinuousAddMonoidHom

namespace ContinuousAddMonoidHom

/-- The horizontal subgroup of the product of the reals and the integers. -/
private def realIntHorizontal : AddSubgroup (ℝ × ℤ) :=
  (snd ℝ ℤ).toAddMonoidHom.ker

private theorem realIntHorizontal_isOpen : IsOpen (realIntHorizontal : Set (ℝ × ℤ)) := by
  have hset : (realIntHorizontal : Set (ℝ × ℤ)) =
      (Prod.snd : ℝ × ℤ → ℤ) ⁻¹' {0} := by
    ext x
    exact AddMonoidHom.mem_ker
  rw [hset]
  exact (isOpen_discrete ({0} : Set ℤ)).preimage continuous_snd

private def realIntSecond : (ℝ × ℤ) →ₜ+ ℝ where
  toFun x := (x.2 : ℝ)
  map_zero' := Int.cast_zero
  map_add' x y := Int.cast_add x.2 y.2
  continuous_toFun := continuous_of_discreteTopology.comp continuous_snd

private def realIntKernelElement :
    {f : (ℝ × ℤ) →ₜ+ ℝ // realIntHorizontal ≤ f.toAddMonoidHom.ker} :=
  ⟨realIntSecond, fun x hx ↦ AddMonoidHom.mem_ker.mpr <| by
    have hx' : x.2 = 0 := AddMonoidHom.mem_ker.mp hx
    exact show (x.2 : ℝ) = 0 by rw [hx', Int.cast_zero]⟩

private noncomputable def realIntQuotientHom :
    ((ℝ × ℤ) ⧸ realIntHorizontal) →ₜ+ ℝ :=
  (quotientAddGroupPullbackHomeomorph realIntHorizontal realIntHorizontal_isOpen).symm
    realIntKernelElement

-- The descent is on the stock quotient, not on a replacement integer carrier.
example : realIntQuotientHom ≠ 0 := by
  have hvalue : realIntQuotientHom (QuotientAddGroup.mk (0, 1)) = 1 :=
    (quotientAddGroupPullbackHomeomorph_symm_apply_mk realIntHorizontal
      realIntHorizontal_isOpen realIntKernelElement (0, 1)).trans Int.cast_one
  intro hzero
  rw [hzero] at hvalue
  exact zero_ne_one hvalue

example (g : ((ℝ × ℤ) ⧸ realIntHorizontal) →ₜ+ ℝ)
    (hg : ∀ x : ℝ × ℤ, g (QuotientAddGroup.mk x) = (x.2 : ℝ)) :
    realIntQuotientHom = g := by
  apply (quotientAddGroupPullbackHomeomorph_symm_eq_iff realIntHorizontal
    realIntHorizontal_isOpen realIntKernelElement g).2
  ext x
  exact (hg x).symm

example : Continuous (fun f :
    {f : (ℝ × ℤ) →ₜ+ ℝ // realIntHorizontal ≤ f.toAddMonoidHom.ker} ↦
    (quotientAddGroupPullbackHomeomorph realIntHorizontal realIntHorizontal_isOpen).symm f) :=
  (continuous_quotientAddGroupPullbackHomeomorph_symm_iff realIntHorizontal
    realIntHorizontal_isOpen
      (fun f : {f : (ℝ × ℤ) →ₜ+ ℝ // realIntHorizontal ≤ f.toAddMonoidHom.ker} ↦ f)).2
    continuous_subtype_val

-- A nonzero integer character survives, while a real-coordinate character is excluded.
private noncomputable def realIntCircleSecond : (ℝ × ℤ) →ₜ+ AddCircle (1 : ℝ) where
  toFun x := x.2 • ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  map_zero' := zero_zsmul _
  map_add' x y := add_zsmul _ x.2 y.2
  continuous_toFun := (continuous_of_discreteTopology :
    Continuous (fun n : ℤ => n • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)))).comp continuous_snd

private theorem realIntCircleSecond_apply (x : ℝ × ℤ) :
    realIntCircleSecond x = x.2 • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := rfl

private noncomputable def realIntCircleFirst : (ℝ × ℤ) →ₜ+ AddCircle (1 : ℝ) where
  toAddMonoidHom := (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (fst ℝ ℤ).toAddMonoidHom
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst

private theorem circleHalf_ne_zero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  intro h
  have hz : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := (1 / 2 : ℝ)) (by norm_num)).mp h
  norm_num at hz

example :
    IsCompact {f : (ℝ × ℤ) →ₜ+ AddCircle (1 : ℝ) |
      realIntHorizontal ≤ f.toAddMonoidHom.ker} ∧
    realIntHorizontal ≤ realIntCircleSecond.toAddMonoidHom.ker ∧
    realIntCircleSecond ≠ 0 ∧
    ¬ realIntHorizontal ≤ realIntCircleFirst.toAddMonoidHom.ker := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  refine ⟨isCompact_setOf_le_ker realIntHorizontal realIntHorizontal_isOpen, ?_, ?_, ?_⟩
  · intro x hx
    apply AddMonoidHom.mem_ker.mpr
    have hx' : x.2 = 0 := AddMonoidHom.mem_ker.mp hx
    have heval : realIntCircleSecond.toAddMonoidHom x =
        x.2 • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := rfl
    rw [heval, hx', zero_zsmul]
  · intro hzero
    have h := DFunLike.congr_fun hzero (0, 1)
    exact circleHalf_ne_zero (by simpa [realIntCircleSecond_apply] using h)
  · intro h
    have hx : ((1 / 2 : ℝ), (0 : ℤ)) ∈ realIntHorizontal :=
      AddMonoidHom.mem_ker.mpr rfl
    exact circleHalf_ne_zero (AddMonoidHom.mem_ker.mp (h hx))

end ContinuousAddMonoidHom
