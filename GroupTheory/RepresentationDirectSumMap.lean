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

A family of intertwiners from the summands to one representation extends uniquely to
an intertwiner from the direct sum. The underlying linear map is Mathlib's
`DirectSum.toModule`; its values on the stock injections characterize it among all
bundled intertwiners. This ambient universal property is separate from the universal
property for arbitrary linear maps on fixed-vector fibers, which needs no target action
and no extension to the ambient modules.

Assembly and restriction along the summand injections form an additive equivalence.
It preserves componentwise addition over an arbitrary semiring; no scalar module
structure on the spaces of intertwiners is needed.
-/

public section

open scoped DirectSum

universe uR uG uI uM uN uA

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

section UniversalProperty

variable {A : Type uA} [AddCommMonoid A] [Module R A]

-- Index decidability is used only internally for the stock direct-sum injections.
attribute [local instance_reducible] Classical.typeDecidableEq
attribute [local instance] Classical.typeDecidableEq

/-- A family of intertwiners to one representation extends to the direct sum. -/
noncomputable def directSumDesc
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h : ∀ i, IntertwiningMap (ρ i) σ) :
    IntertwiningMap (directSum ρ) σ := by
  refine ⟨DirectSum.toModule R I A (fun i => (h i : M i →ₗ[R] A)), ?_⟩
  intro g
  apply DirectSum.linearMap_ext
  intro i
  ext v
  have hi : (h i : M i →ₗ[R] A).comp ((ρ i) g) =
      (σ g).comp (h i : M i →ₗ[R] A) := by
    rcases h i with ⟨hi, hcomm⟩
    exact hcomm g
  simpa only [LinearMap.comp_apply, directSum_apply, DirectSum.lmap_lof,
    DirectSum.toModule_lof] using
    congrArg (fun L : M i →ₗ[R] A => L v) hi

/-- The underlying linear map of the extension is the stock direct-sum eliminator. -/
@[simp] theorem directSumDesc_toLinearMap
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h : ∀ i, IntertwiningMap (ρ i) σ) :
    (directSumDesc ρ σ h).toLinearMap =
      DirectSum.toModule R I A (fun i => (h i : M i →ₗ[R] A)) := by
  rfl

/-- The extension restricts to the supplied intertwiner on each summand. -/
@[simp] theorem directSumDesc_lof
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h : ∀ i, IntertwiningMap (ρ i) σ) (i : I) (v : M i) :
    directSumDesc ρ σ h (DirectSum.lof R I M i v) = h i v := by
  change (directSumDesc ρ σ h).toLinearMap (DirectSum.lof R I M i v) = _
  rw [directSumDesc_toLinearMap, DirectSum.toModule_lof]
  rcases h i with ⟨hi, hcomm⟩
  rfl

/-- Any bundled intertwiner with the supplied values on all summands is the extension. -/
theorem directSumDesc_unique
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h : ∀ i, IntertwiningMap (ρ i) σ)
    (K : IntertwiningMap (directSum ρ) σ)
    (hK : ∀ (i : I) (v : M i), K (DirectSum.lof R I M i v) = h i v) :
    K = directSumDesc ρ σ h := by
  have hlinear : K.toLinearMap = (directSumDesc ρ σ h).toLinearMap := by
    rw [directSumDesc_toLinearMap]
    apply DirectSum.linearMap_ext
    intro i
    ext v
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
    have hv := hK i v
    rcases K with ⟨k, hk⟩
    generalize hhi : h i = h' at hv ⊢
    rcases h' with ⟨hi, hcomm⟩
    exact hv
  apply DFunLike.ext
  intro x
  change K.toLinearMap x = (directSumDesc ρ σ h).toLinearMap x
  exact congrArg (fun L : (⨁ i, M i) →ₗ[R] A => L x) hlinear

/-- Restriction of an outgoing intertwiner to one summand. -/
private noncomputable def directSumRestrict
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (K : IntertwiningMap (directSum ρ) σ) (i : I) :
    IntertwiningMap (ρ i) σ := by
  refine ⟨K.toLinearMap.comp (DirectSum.lof R I M i), ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  have hK : K.toLinearMap.comp ((directSum ρ) g) =
      (σ g).comp K.toLinearMap := by
    rcases K with ⟨k, hcomm⟩
    exact hcomm g
  simpa only [LinearMap.comp_apply, directSum_apply, DirectSum.lmap_lof] using
    congrArg (fun L : (⨁ i, M i) →ₗ[R] A => L (DirectSum.lof R I M i v)) hK

private theorem directSumRestrict_apply
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (K : IntertwiningMap (directSum ρ) σ) (i : I) (v : M i) :
    directSumRestrict ρ σ K i v = K (DirectSum.lof R I M i v) := by
  change (K.toLinearMap.comp (DirectSum.lof R I M i)) v = _
  rw [LinearMap.comp_apply]
  rcases K with ⟨k, hcomm⟩
  rfl

/-- Assembly and restriction along the summand injections give an additive equivalence
between families of intertwiners and intertwiners out of the direct sum. -/
noncomputable def directSumDescAddEquiv
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A) :
    (∀ i, IntertwiningMap (ρ i) σ) ≃+ IntertwiningMap (directSum ρ) σ where
  toFun := directSumDesc ρ σ
  invFun := fun K i => directSumRestrict ρ σ K i
  left_inv := by
    intro h
    funext i
    apply DFunLike.ext
    intro v
    rw [directSumRestrict_apply, directSumDesc_lof]
  right_inv := by
    intro K
    symm
    apply directSumDesc_unique ρ σ (fun i => directSumRestrict ρ σ K i) K
    intro i v
    exact (directSumRestrict_apply ρ σ K i v).symm
  map_add' := by
    intro h k
    symm
    apply directSumDesc_unique ρ σ (h + k)
    intro i v
    simp

/-- The forward additive equivalence is the canonical bundled extension. -/
@[simp] theorem directSumDescAddEquiv_apply
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h : ∀ i, IntertwiningMap (ρ i) σ) :
    directSumDescAddEquiv ρ σ h = directSumDesc ρ σ h := by
  rfl

/-- The inverse additive equivalence restricts to the original summand injection. -/
@[simp] theorem directSumDescAddEquiv_symm_apply
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (K : IntertwiningMap (directSum ρ) σ) (i : I) (v : M i) :
    (directSumDescAddEquiv ρ σ).symm K i v = K (DirectSum.lof R I M i v) := by
  exact directSumRestrict_apply ρ σ K i v

/-- Extension commutes with componentwise addition of the original intertwiners. -/
@[simp] theorem directSumDesc_add
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A)
    (h k : ∀ i, IntertwiningMap (ρ i) σ) :
    directSumDesc ρ σ (h + k) = directSumDesc ρ σ h + directSumDesc ρ σ k := by
  simpa only [directSumDescAddEquiv_apply] using
    (directSumDescAddEquiv ρ σ).map_add h k

/-- The zero family extends to the zero outgoing intertwiner. -/
@[simp] theorem directSumDesc_zero
    (ρ : ∀ i, Representation R G (M i)) (σ : Representation R G A) :
    directSumDesc ρ σ (0 : ∀ i, IntertwiningMap (ρ i) σ) = 0 := by
  simpa only [directSumDescAddEquiv_apply] using
    map_zero (directSumDescAddEquiv ρ σ)

end UniversalProperty

end IntertwiningMap

end Representation
