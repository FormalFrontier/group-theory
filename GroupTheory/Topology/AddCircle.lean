/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Additive circle equivalences and character transport

Mathlib's homeomorphism from `AddCircle T` to `Circle` preserves addition after
retagging the target as `Additive Circle`, with its inherited topology and group
operations. The resulting continuous additive equivalence is valid for every
nonzero real period, including negative periods. On real representatives its map
is `x ↦ exp (2 * π / T * x)`.

For period one, postcomposition gives a continuous additive equivalence between
the corresponding spaces of continuous additive characters of any topological
additive monoid. No continuity of the operation on the domain is needed.
-/

@[expose] public section

universe u

namespace AddCircle

variable {T : ℝ}

/-- The continuous additive equivalence from `ℝ / ℤ • T` to the additive unit circle.
Its map on real representatives is `x ↦ exp (2 * π / T * x)`.
This bundles Mathlib's `AddCircle.homeomorphCircle` and `AddCircle.toCircle_add`. -/
noncomputable def continuousAddEquivCircle (hT : T ≠ 0) :
    AddCircle T ≃ₜ+ Additive Circle :=
  ContinuousAddEquiv.mk'
    { toEquiv := (homeomorphCircle hT).toEquiv
      continuous_toFun := (homeomorphCircle hT).continuous_toFun
      continuous_invFun := (homeomorphCircle hT).continuous_invFun }
    (by
      intro x y
      exact congrArg (Additive.ofMul : Circle → Additive Circle)
        ((homeomorphCircle_apply hT (x + y)).trans <|
          (toCircle_add x y).trans <|
            congrArg₂ (· * ·) (homeomorphCircle_apply hT x).symm
              (homeomorphCircle_apply hT y).symm))

@[simp]
theorem continuousAddEquivCircle_apply (hT : T ≠ 0) (x : AddCircle T) :
    continuousAddEquivCircle hT x = Additive.ofMul (toCircle x) :=
  homeomorphCircle_apply hT x

@[simp]
theorem continuousAddEquivCircle_symm_apply (hT : T ≠ 0) (x : Additive Circle) :
    (continuousAddEquivCircle hT).symm x = (homeomorphCircle hT).symm x.toMul := rfl

/-- On real representatives the additive equivalence has the same normalization as
Mathlib's circle map; in particular period one gives `x ↦ exp (2 * π * x)`. -/
theorem continuousAddEquivCircle_apply_coe (hT : T ≠ 0) (x : ℝ) :
    continuousAddEquivCircle hT (x : AddCircle T) =
      Additive.ofMul (Circle.exp (2 * Real.pi / T * x)) := by
  rw [continuousAddEquivCircle_apply, toCircle_apply_mk]

/-- Transport period-one additive-circle characters to additive unit-circle characters
by postcomposition, preserving their pointwise addition and compact-open topology. -/
noncomputable def continuousAddMonoidHomEquivCircle (A : Type u) [AddMonoid A]
    [TopologicalSpace A] :
    (A →ₜ+ AddCircle (1 : ℝ)) ≃ₜ+ (A →ₜ+ Additive Circle) :=
  ContinuousAddEquiv.continuousAddMonoidHomCongrRight A
    (continuousAddEquivCircle one_ne_zero)

@[simp]
theorem continuousAddMonoidHomEquivCircle_apply (A : Type u) [AddMonoid A]
    [TopologicalSpace A] (χ : A →ₜ+ AddCircle (1 : ℝ)) (a : A) :
    continuousAddMonoidHomEquivCircle A χ a = Additive.ofMul (toCircle (χ a)) :=
  continuousAddEquivCircle_apply one_ne_zero (χ a)

@[simp]
theorem continuousAddMonoidHomEquivCircle_symm_apply (A : Type u) [AddMonoid A]
    [TopologicalSpace A] (χ : A →ₜ+ Additive Circle) (a : A) :
    (continuousAddMonoidHomEquivCircle A).symm χ a =
      (continuousAddEquivCircle one_ne_zero).symm (χ a) := rfl

end AddCircle
