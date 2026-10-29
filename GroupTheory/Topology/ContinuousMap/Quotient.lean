/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.ContinuousMap.CompactCovering

/-!
# Descent of continuous maps along compact-covering quotient maps

Pullback along a quotient map identifies continuous maps on the quotient with continuous maps
constant on its fibres. If every compact set is the exact image of a compact set, this
identification is a homeomorphism for the compact-open topology and its inherited subtype topology.
-/

@[expose] public section

open Set Topology

universe u v w z

variable {X : Type u} {Y : Type v} {T : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]

namespace Topology.IsQuotientMap

/-- Descent along a compact-covering quotient map is continuous for the compact-open topology. -/
theorem continuous_liftEquiv_of_compactCovering {q : C(X, Y)} (hq : IsQuotientMap q)
    (hcover : ∀ K : Set Y, IsCompact K → ∃ L : Set X, IsCompact L ∧ q '' L = K) :
    Continuous (hq.liftEquiv : {g : C(X, T) // Function.FactorsThrough g q} → C(Y, T)) := by
  have hEmb := ContinuousMap.isEmbedding_precomp_of_compactCovering (T := T) q hcover
  apply hEmb.isInducing.continuous_iff.mpr
  change Continuous (fun g : {g : C(X, T) // Function.FactorsThrough g q} ↦
    (hq.liftEquiv g).comp q)
  have hcomp : (fun g : {g : C(X, T) // Function.FactorsThrough g q} ↦
      (hq.liftEquiv g).comp q) = Subtype.val := by
    funext g
    exact hq.lift_comp g.val g.property
  rw [hcomp]
  exact continuous_subtype_val

end Topology.IsQuotientMap

namespace ContinuousMap

/-- Pullback along a compact-covering quotient map, with the inherited compact-open topology
on the subtype of maps constant on its fibres. -/
noncomputable def quotientPullbackHomeomorph (q : C(X, Y)) (hq : IsQuotientMap q)
    (hcover : ∀ K : Set Y, IsCompact K → ∃ L : Set X, IsCompact L ∧ q '' L = K) :
    C(Y, T) ≃ₜ {g : C(X, T) // Function.FactorsThrough g q} where
  toEquiv := hq.liftEquiv.symm
  continuous_toFun := (continuous_precomp q).subtype_mk
    (fun g ↦ (hq.liftEquiv.symm g).property)
  continuous_invFun := hq.continuous_liftEquiv_of_compactCovering hcover

variable (q : C(X, Y)) (hq : IsQuotientMap q)
  (hcover : ∀ K : Set Y, IsCompact K → ∃ L : Set X, IsCompact L ∧ q '' L = K)

@[simp]
theorem coe_quotientPullbackHomeomorph_apply (f : C(Y, T)) :
    (quotientPullbackHomeomorph q hq hcover f).val = f.comp q := rfl

@[simp]
theorem quotientPullbackHomeomorph_apply_apply (f : C(Y, T)) (x : X) :
    (quotientPullbackHomeomorph q hq hcover f).val x = f (q x) := rfl

@[simp]
theorem quotientPullbackHomeomorph_symm_apply
    (g : {g : C(X, T) // Function.FactorsThrough g q}) :
    (quotientPullbackHomeomorph q hq hcover).symm g = hq.lift g.val g.property := rfl

theorem quotientPullbackHomeomorph_symm_comp
    (g : {g : C(X, T) // Function.FactorsThrough g q}) :
    ((quotientPullbackHomeomorph q hq hcover).symm g).comp q = g.val :=
  hq.lift_comp g.val g.property

theorem quotientPullbackHomeomorph_symm_apply_apply
    (g : {g : C(X, T) // Function.FactorsThrough g q}) (x : X) :
    (quotientPullbackHomeomorph q hq hcover).symm g (q x) = g.val x :=
  DFunLike.congr_fun (quotientPullbackHomeomorph_symm_comp q hq hcover g) x

/-- A descended map is uniquely determined by its composite with the quotient map. -/
theorem quotientPullbackHomeomorph_symm_eq_iff
    (g : {g : C(X, T) // Function.FactorsThrough g q}) (f : C(Y, T)) :
    (quotientPullbackHomeomorph q hq hcover).symm g = f ↔ g.val = f.comp q := by
  constructor
  · rintro rfl
    exact (quotientPullbackHomeomorph_symm_comp q hq hcover g).symm
  · intro h
    exact (cancel_right hq.surjective).mp
      ((quotientPullbackHomeomorph_symm_comp q hq hcover g).trans h)

/-- A family of descended maps is continuous exactly when the original family is continuous
as a family in the ambient compact-open space, not merely pointwise. -/
theorem continuous_quotientPullbackHomeomorph_symm_iff
    {S : Type z} [TopologicalSpace S]
    (F : S → {g : C(X, T) // Function.FactorsThrough g q}) :
    Continuous (fun s ↦ (quotientPullbackHomeomorph q hq hcover).symm (F s)) ↔
      Continuous (fun s ↦ (F s).val) := by
  constructor
  · intro hF
    simpa only [Function.comp_def, quotientPullbackHomeomorph_symm_comp] using
      (continuous_precomp q).comp hF
  · intro hF
    exact (quotientPullbackHomeomorph q hq hcover).symm.continuous.comp
      (hF.subtype_mk fun s ↦ (F s).property)

/-- A continuous right inverse supplies exact compact lifts without requiring the source
or the quotient to be compact. -/
noncomputable def quotientPullbackHomeomorphOfRightInverse
    (s : C(Y, X)) (hs : Function.RightInverse s q) :
    C(Y, T) ≃ₜ {g : C(X, T) // Function.FactorsThrough g q} :=
  quotientPullbackHomeomorph q
    (IsQuotientMap.of_inverse (map_continuous s) (map_continuous q) hs)
    (fun K hK ↦ ⟨s '' K, hK.image (map_continuous s), by
      rw [← Set.image_comp, hs.comp_eq_id, Set.image_id]⟩)

@[simp]
theorem quotientPullbackHomeomorphOfRightInverse_symm_apply
    (s : C(Y, X)) (hs : Function.RightInverse s q)
    (g : {g : C(X, T) // Function.FactorsThrough g q}) (y : Y) :
    (quotientPullbackHomeomorphOfRightInverse q s hs).symm g y = g.val (s y) := by
  have hq : IsQuotientMap q := IsQuotientMap.of_inverse (map_continuous s) (map_continuous q) hs
  have h : (quotientPullbackHomeomorphOfRightInverse q s hs).symm g (q (s y)) =
      g.val (s y) := DFunLike.congr_fun (hq.lift_comp g.val g.property) (s y)
  simpa only [hs y] using h

end ContinuousMap
