/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants

/-!
# Fixed vectors in direct sums of representations

For a family of representations over a semiring, the fixed vectors in its algebraic
direct sum are canonically linearly equivalent to the direct sum of its fixed-vector
submodules. The equivalence is characterized on coefficients in both directions.

The outgoing universal property allows arbitrary linear maps from the fixed-vector
fibers to a module, without requiring extensions to the ambient representation spaces
or an action on the target. Its extension is the composite of `DirectSum.toModule`
with `Representation.directSumFixedSubmoduleLinearEquiv`.

The construction reuses Mathlib's injectivity and range theorems for `DirectSum.lmap`
and the equivalence of a linear map's domain with its range.
-/

public section

open scoped DirectSum

universe uR uG uI uM uA

namespace Representation

variable {R : Type uR} [Semiring R] {G : Type uG} [Monoid G]
  {I : Type uI} {M : I → Type uM}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The direct sum of submodules, identified with the coefficientwise submodule. -/
private noncomputable def directSumSubmoduleLinearEquiv
    (p : ∀ i, Submodule R (M i)) :
    (⨁ i, p i) ≃ₗ[R]
      (Submodule.pi Set.univ p).comap (DirectSum.coeFnLinearMap R) := by
  let J : (⨁ i, p i) →ₗ[R] (⨁ i, M i) :=
    DirectSum.lmap (fun i => (p i).subtype)
  have hJ : Function.Injective J :=
    (DirectSum.lmap_injective (fun i => (p i).subtype)).2
      (fun i => Subtype.val_injective)
  have hRange : LinearMap.range J =
      (Submodule.pi Set.univ p).comap (DirectSum.coeFnLinearMap R) := by
    simpa only [J, Submodule.range_subtype] using
      (DirectSum.range_lmap (fun i => (p i).subtype))
  exact (LinearEquiv.ofInjective J hJ).trans (LinearEquiv.ofEq _ _ hRange)

private theorem directSumSubmoduleLinearEquiv_coe
    (p : ∀ i, Submodule R (M i)) (y : ⨁ i, p i) :
    ((directSumSubmoduleLinearEquiv p y :
      (Submodule.pi Set.univ p).comap (DirectSum.coeFnLinearMap R)) : ⨁ i, M i) =
      DirectSum.lmap (fun i => (p i).subtype) y := by
  simp only [directSumSubmoduleLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

private theorem directSum_fixedSubmodule_eq
    (ρ : ∀ i, Representation R G (M i)) :
    (directSum ρ).fixedSubmodule =
      (Submodule.pi Set.univ (fun i => (ρ i).fixedSubmodule)).comap
        (DirectSum.coeFnLinearMap R) := by
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_const,
    DirectSum.coeFnLinearMap_apply, mem_fixedSubmodule]
  constructor
  · intro hx i g
    have hg := congrArg (fun v : ⨁ i, M i => v i) (hx g)
    simpa only [directSum_apply, DirectSum.lmap_apply] using hg
  · intro hx g
    ext i
    simpa only [directSum_apply, DirectSum.lmap_apply] using hx i g

/-- Fixed vectors in a direct sum are the direct sum of the fixed-vector submodules.

No finiteness assumption on the index type or invertibility assumption on the acting
monoid is needed. -/
noncomputable def directSumFixedSubmoduleLinearEquiv
    (ρ : ∀ i, Representation R G (M i)) :
    (directSum ρ).fixedSubmodule ≃ₗ[R] (⨁ i, (ρ i).fixedSubmodule) := by
  exact ((directSumSubmoduleLinearEquiv (fun i => (ρ i).fixedSubmodule)).trans
    (LinearEquiv.ofEq _ _ (directSum_fixedSubmodule_eq ρ).symm)).symm

/-- The inverse equivalence includes every fixed fiber by its submodule inclusion. -/
theorem directSumFixedSubmoduleLinearEquiv_symm_coe
    (ρ : ∀ i, Representation R G (M i)) (y : ⨁ i, (ρ i).fixedSubmodule) :
    ((directSumFixedSubmoduleLinearEquiv ρ).symm y : ⨁ i, M i) =
      DirectSum.lmap (fun i => (ρ i).fixedSubmodule.subtype) y := by
  simp only [directSumFixedSubmoduleLinearEquiv, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    directSumSubmoduleLinearEquiv_coe]

/-- The inverse equivalence preserves each coefficient in the ambient module. -/
@[simp] theorem directSumFixedSubmoduleLinearEquiv_symm_apply
    (ρ : ∀ i, Representation R G (M i)) (y : ⨁ i, (ρ i).fixedSubmodule) (i : I) :
    (((directSumFixedSubmoduleLinearEquiv ρ).symm y : ⨁ j, M j) i) = (y i : M i) := by
  simp only [directSumFixedSubmoduleLinearEquiv_symm_coe, DirectSum.lmap_apply,
    Submodule.subtype_apply]

/-- The equivalence preserves each coefficient in the ambient module. -/
@[simp] theorem directSumFixedSubmoduleLinearEquiv_apply
    (ρ : ∀ i, Representation R G (M i)) (x : (directSum ρ).fixedSubmodule) (i : I) :
    ((directSumFixedSubmoduleLinearEquiv ρ x) i : M i) = (x : ⨁ j, M j) i := by
  have h := directSumFixedSubmoduleLinearEquiv_symm_apply ρ
    (directSumFixedSubmoduleLinearEquiv ρ x) i
  simpa only [LinearEquiv.symm_apply_apply] using h.symm

section UniversalProperty

variable {A : Type uA} [AddCommMonoid A] [Module R A]

-- Only the stock direct-sum injections and eliminator need index decidability.
attribute [local instance_reducible] Classical.typeDecidableEq
attribute [local instance] Classical.typeDecidableEq

/-- Arbitrary maps from the fixed fibers extend along the canonical fixed-vector
injections. No map on an ambient representation space is required. -/
theorem directSumFixedSubmoduleLinearEquiv_toModule_lof
    (ρ : ∀ i, Representation R G (M i))
    (h : ∀ i, (ρ i).fixedSubmodule →ₗ[R] A) (i : I) (v : (ρ i).fixedSubmodule) :
    ((DirectSum.toModule R I A h).comp
      (directSumFixedSubmoduleLinearEquiv ρ).toLinearMap)
        ((directSumFixedSubmoduleLinearEquiv ρ).symm
          (DirectSum.lof R I (fun j => (ρ j).fixedSubmodule) i v)) = h i v := by
  calc
    _ = (DirectSum.toModule R I A h)
        (DirectSum.lof R I (fun j => (ρ j).fixedSubmodule) i v) :=
      congrArg (DirectSum.toModule R I A h)
        ((directSumFixedSubmoduleLinearEquiv ρ).apply_symm_apply _)
    _ = h i v := by rw [DirectSum.toModule_lof]

/-- Every linear map out of the fixed submodule is determined by its restrictions to
all fixed fibers. The resulting extension is the stock direct-sum eliminator composed
with the canonical equivalence. -/
theorem directSumFixedSubmoduleLinearEquiv_toModule_unique
    (ρ : ∀ i, Representation R G (M i))
    (h : ∀ i, (ρ i).fixedSubmodule →ₗ[R] A)
    (K : (directSum ρ).fixedSubmodule →ₗ[R] A)
    (hK : ∀ i, K.comp
      ((directSumFixedSubmoduleLinearEquiv ρ).symm.toLinearMap.comp
        (DirectSum.lof R I (fun j => (ρ j).fixedSubmodule) i)) = h i) :
    K = (DirectSum.toModule R I A h).comp
      (directSumFixedSubmoduleLinearEquiv ρ).toLinearMap := by
  have hcomp : K.comp (directSumFixedSubmoduleLinearEquiv ρ).symm.toLinearMap =
      DirectSum.toModule R I A h := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    have hv := congrArg (fun L : (ρ i).fixedSubmodule →ₗ[R] A => L v) (hK i)
    simpa only [LinearMap.comp_apply, DirectSum.toModule_lof] using hv
  ext x
  calc
    K x = K ((directSumFixedSubmoduleLinearEquiv ρ).symm
        (directSumFixedSubmoduleLinearEquiv ρ x)) :=
      congrArg K ((directSumFixedSubmoduleLinearEquiv ρ).symm_apply_apply x).symm
    _ = _ := congrArg (fun L : (⨁ i, (ρ i).fixedSubmodule) →ₗ[R] A =>
      L (directSumFixedSubmoduleLinearEquiv ρ x)) hcomp

end UniversalProperty

end Representation
