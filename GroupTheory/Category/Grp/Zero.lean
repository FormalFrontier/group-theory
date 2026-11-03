/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Category.Mon.Zero
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Zero morphisms of groups

The constant-one morphisms give zero morphisms for arbitrary, not necessarily
commutative, groups. These are induced by the monoid zero morphisms. The zero
object remains the existing `GrpCat` zero object from Mathlib.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace GrpCat

/-- The constant-one homomorphisms give zero morphisms of groups. -/
instance constantOneHasZeroMorphisms : HasZeroMorphisms GrpCat.{u} where
  zero G H := ⟨ofHom (0 : MonCat.of G ⟶ MonCat.of H).hom⟩
  comp_zero := by
    intro X Y f Z
    apply GrpCat.ext
    intro x
    rfl
  zero_comp := by
    intro X Y Z f
    apply GrpCat.ext
    intro x
    exact f.hom.map_one

/-- The homomorphism underlying a zero group morphism is constant one. -/
@[simp] theorem zero_hom {G H : GrpCat.{u}} : (0 : G ⟶ H).hom = 1 := by
  rfl

/-- A zero morphism of groups takes every element to one. -/
theorem zero_apply {G H : GrpCat.{u}} (g : G) : (0 : G ⟶ H) g = 1 := by
  rfl

end GrpCat
