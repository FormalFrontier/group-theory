/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.ContinuousMonoidHom.Quotient
import Mathlib.Topology.Algebra.Ring.Real

/-! The real first projection has a continuous zero section. Its compact lifts are section
images, so compactness of the source or quotient is unnecessary. The inverse below descends
arbitrary fibreconstant original continuous additive homomorphisms. -/

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
