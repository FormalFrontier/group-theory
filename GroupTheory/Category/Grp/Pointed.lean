/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Category.Mon.Pointed
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Groups as pointed types

A group is pointed by one. The forgetful functor factors through the category
of monoids and does not require commutativity.
-/

@[expose] public section

open CategoryTheory

universe u

namespace GrpCat

/-- The underlying pointed type of a group, with distinguished element one. -/
def toPointed : GrpCat.{u} ⥤ Pointed.{u} :=
  forget₂ GrpCat MonCat ⋙ MonCat.toPointed

/-- The pointed group functor factors through the monoid forgetful functor. -/
theorem toPointed_eq_forget₂_comp :
    toPointed.{u} = forget₂ GrpCat MonCat ⋙ MonCat.toPointed := by
  rfl

/-- Forgetting a group to its pointed underlying type. -/
instance hasForgetToPointed : HasForget₂ GrpCat.{u} Pointed.{u} where
  forget₂ := toPointed
  forget_comp := by rfl

/-- The canonical pointed forgetful functor agrees with `GrpCat.toPointed`. -/
theorem forget₂_toPointed : forget₂ GrpCat.{u} Pointed.{u} = toPointed := by
  rfl

/-- Forgetting the distinguished point recovers the original group forgetful functor. -/
theorem toPointed_comp_forget : toPointed.{u} ⋙ forget Pointed = forget GrpCat := by
  exact HasForget₂.forget_comp

/-- The whole pointed object is the original group pointed by one. -/
theorem toPointed_obj (G : GrpCat.{u}) : toPointed.obj G = Pointed.of (1 : G) := by
  rfl

/-- The underlying type of the pointed group is the original carrier. -/
theorem toPointed_obj_coe (G : GrpCat.{u}) : ↥(toPointed.obj G) = G := by
  rfl

/-- The distinguished point of a group is one. -/
@[simp] theorem toPointed_obj_point (G : GrpCat.{u}) : (toPointed.obj G).point = (1 : G) := by
  rfl

/-- The pointed map of a group homomorphism is its underlying function. -/
@[simp] theorem toPointed_map_toFun {G H : GrpCat.{u}} (f : G ⟶ H) :
    (toPointed.map f).toFun = (f : G → H) := by
  rfl

end GrpCat
