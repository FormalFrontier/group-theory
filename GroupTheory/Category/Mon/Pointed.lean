/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.CategoryTheory.Category.Pointed

/-!
# Monoids as pointed types

A monoid is pointed by one, and monoid homomorphisms preserve this point.
-/

@[expose] public section

open CategoryTheory

universe u

namespace MonCat

/-- The underlying pointed type of a monoid, with distinguished element one. -/
def toPointed : MonCat.{u} ⥤ Pointed.{u} where
  obj M := Pointed.of (1 : M)
  map f := ⟨f, f.hom.map_one⟩
  map_id _ := by
    apply Pointed.Hom.ext
    rfl
  map_comp _ _ := by
    apply Pointed.Hom.ext
    rfl

/-- Forgetting a monoid to its pointed underlying type. -/
instance hasForgetToPointed : HasForget₂ MonCat.{u} Pointed.{u} where
  forget₂ := toPointed
  forget_comp := by rfl

/-- The canonical pointed forgetful functor agrees with `MonCat.toPointed`. -/
theorem forget₂_toPointed : forget₂ MonCat.{u} Pointed.{u} = toPointed := by
  rfl

/-- Forgetting the distinguished point recovers the original monoid forgetful functor. -/
theorem toPointed_comp_forget : toPointed.{u} ⋙ forget Pointed = forget MonCat := by
  exact HasForget₂.forget_comp

/-- The whole pointed object is the original monoid pointed by one. -/
theorem toPointed_obj (M : MonCat.{u}) : toPointed.obj M = Pointed.of (1 : M) := by
  rfl

/-- The underlying type of the pointed monoid is the original carrier. -/
theorem toPointed_obj_coe (M : MonCat.{u}) : ↥(toPointed.obj M) = M := by
  rfl

/-- The distinguished point of a monoid is one. -/
@[simp] theorem toPointed_obj_point (M : MonCat.{u}) : (toPointed.obj M).point = (1 : M) := by
  rfl

/-- The pointed map of a monoid homomorphism is its underlying function. -/
@[simp] theorem toPointed_map_toFun {M N : MonCat.{u}} (f : M ⟶ N) :
    (toPointed.map f).toFun = (f : M → N) := by
  rfl

end MonCat
