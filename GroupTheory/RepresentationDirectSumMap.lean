/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationDirectSum

/-!
# Maps of direct sums of representations

A family of bundled intertwining maps induces a bundled intertwining map of the
algebraic direct sums. Its underlying linear map is the stock `DirectSum.lmap` of
the original family, and its coefficients and generators are mapped fiberwise.
The canonical fixed-vector direct-sum equivalence is natural with respect to this map.
-/

public section

open scoped DirectSum

universe uR uG uI uM uN

namespace Representation

variable {R : Type uR} [Semiring R] {G : Type uG} [Monoid G]
  {I : Type uI} {M : I → Type uM} {N : I → Type uN}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

namespace IntertwiningMap

/-- The direct sum of the original family of bundled intertwining maps. -/
noncomputable def directSumFamily
    (ρ : ∀ i, Representation R G (M i)) (τ : ∀ i, Representation R G (N i))
    (f : ∀ i, IntertwiningMap (ρ i) (τ i)) :
    IntertwiningMap (directSum ρ) (directSum τ) := by
  refine ⟨DirectSum.lmap (fun i => (f i : M i →ₗ[R] N i)), ?_⟩
  intro g
  ext x i
  have hi : (f i : M i →ₗ[R] N i).comp ((ρ i) g) =
      ((τ i) g).comp (f i : M i →ₗ[R] N i) := by
    rcases f i with ⟨fi, hfi⟩
    exact hfi g
  simpa only [LinearMap.comp_apply, directSum_apply, DirectSum.lmap_apply] using
    congrArg (fun L : M i →ₗ[R] N i => L (x i)) hi

/-- The underlying linear map is exactly the stock direct-sum linear map. -/
@[simp] theorem directSumFamily_toLinearMap
    (ρ : ∀ i, Representation R G (M i)) (τ : ∀ i, Representation R G (N i))
    (f : ∀ i, IntertwiningMap (ρ i) (τ i)) :
    (directSumFamily ρ τ f).toLinearMap =
      DirectSum.lmap (fun i => (f i : M i →ₗ[R] N i)) := by
  rfl

/-- Each coefficient is mapped by the original intertwining map of that fiber. -/
@[simp] theorem directSumFamily_apply
    (ρ : ∀ i, Representation R G (M i)) (τ : ∀ i, Representation R G (N i))
    (f : ∀ i, IntertwiningMap (ρ i) (τ i)) (x : ⨁ i, M i) (i : I) :
    (directSumFamily ρ τ f x) i = f i (x i) := by
  change ((directSumFamily ρ τ f).toLinearMap x) i = _
  rw [directSumFamily_toLinearMap, DirectSum.lmap_apply]
  rcases f i with ⟨fi, hfi⟩
  rfl

section Generators

-- Index decidability is used only internally for the stock direct-sum injections.
attribute [local instance_reducible] Classical.typeDecidableEq
attribute [local instance] Classical.typeDecidableEq

/-- A generator in one summand is sent to the generator of its original image. -/
@[simp] theorem directSumFamily_lof
    (ρ : ∀ i, Representation R G (M i)) (τ : ∀ i, Representation R G (N i))
    (f : ∀ i, IntertwiningMap (ρ i) (τ i)) (i : I) (v : M i) :
    directSumFamily ρ τ f (DirectSum.lof R I M i v) =
      DirectSum.lof R I N i (f i v) := by
  change (directSumFamily ρ τ f).toLinearMap (DirectSum.lof R I M i v) = _
  rw [directSumFamily_toLinearMap, DirectSum.lmap_lof]
  rcases f i with ⟨fi, hfi⟩
  rfl

end Generators

/-- The fixed-vector direct-sum equivalence is natural with respect to a family of
intertwining maps. -/
theorem directSumFamily_fixedSubmoduleMap
    (ρ : ∀ i, Representation R G (M i)) (τ : ∀ i, Representation R G (N i))
    (f : ∀ i, IntertwiningMap (ρ i) (τ i)) :
    (directSumFixedSubmoduleLinearEquiv τ).toLinearMap.comp
        (directSumFamily ρ τ f).fixedSubmoduleMap =
      (DirectSum.lmap (fun i => (f i).fixedSubmoduleMap)).comp
        (directSumFixedSubmoduleLinearEquiv ρ).toLinearMap := by
  apply LinearMap.ext
  intro x
  change directSumFixedSubmoduleLinearEquiv τ
      ((directSumFamily ρ τ f).fixedSubmoduleMap x) =
    DirectSum.lmap (fun i => (f i).fixedSubmoduleMap)
      (directSumFixedSubmoduleLinearEquiv ρ x)
  apply (directSumFixedSubmoduleLinearEquiv τ).symm.injective
  apply Subtype.ext
  ext i
  simp only [LinearEquiv.symm_apply_apply, fixedSubmoduleMap_apply,
    directSumFamily_apply, directSumFixedSubmoduleLinearEquiv_symm_apply,
    DirectSum.lmap_apply, directSumFixedSubmoduleLinearEquiv_apply]

end IntertwiningMap

end Representation
