/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero morphisms of monoids

The constant-one monoid homomorphisms are zero morphisms in `MonCat`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace MonCat

/-- The constant-one homomorphisms give zero morphisms of monoids. -/
instance constantOneHasZeroMorphisms : HasZeroMorphisms MonCat.{u} where
  zero _ _ := ⟨1⟩
  comp_zero := by
    intro X Y f Z
    apply MonCat.ext
    intro x
    rfl
  zero_comp := by
    intro X Y Z f
    apply MonCat.ext
    intro x
    exact f.hom.map_one

/-- The homomorphism underlying a zero monoid morphism is constant one. -/
@[simp] theorem zero_hom {M N : MonCat.{u}} : (0 : M ⟶ N).hom = 1 := by
  rfl

/-- A zero morphism of monoids takes every element to one. -/
theorem zero_apply {M N : MonCat.{u}} (x : M) : (0 : M ⟶ N) x = 1 := by
  rfl

end MonCat
