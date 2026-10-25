/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.MonoidLocalization.GrothendieckGroup.Ring
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Grothendieck lifts and ring structures

The additive lift of the canonical map from natural numbers to integers sends a difference
of generators to a negative integer. Extending natural-number multiplication in both
variables gives the corresponding negative product on a difference of generators.
The canonical ring structure gives a nonzero signed product on the completion of the
natural numbers, while the completion of the one-element semiring has zero equal to one.
The ring lift of the natural-number cast retains the same additive integer-valued
detector and sends the signed product to negative six. These examples use the
completion's canonical generators without identifying the completion with another model.
-/

@[expose] public section

universe u

namespace GroupTheoryTest.GrothendieckGroup

open Algebra.GrothendieckAddGroup

/-- The additive extension of the natural-number cast evaluates a negative difference. -/
example : liftAddEquiv (Nat.castAddMonoidHom ℤ) (of (M := ℕ) 2 - of 5) = -3 := by
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply]
  rw [liftAddEquiv_apply, map_sub, lift_of, lift_of]
  rfl

private def natMulInt : ℕ →+ ℕ →+ ℤ where
  toFun a :=
    { toFun := fun b ↦ (a : ℤ) * (b : ℤ)
      map_zero' := mul_zero _
      map_add' := fun b c ↦ by rw [Nat.cast_add, mul_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    exact zero_mul (b : ℤ)
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    change ((a + b : ℕ) : ℤ) * (c : ℤ) =
      (a : ℤ) * (c : ℤ) + (b : ℤ) * (c : ℤ)
    rw [Nat.cast_add, add_mul]

/-- The bilinear extension of natural-number multiplication evaluates a negative argument. -/
example : lift₂ natMulInt (of (M := ℕ) 2 - of 5) (of (M := ℕ) 3) = -9 := by
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply]
  rw [map_sub, AddMonoidHom.sub_apply, lift₂_of, lift₂_of]
  rfl

/-- Doubling both inputs and negating the output commutes with bilinear extension,
even on a difference of generators. -/
example :
    lift₂ (((natMulInt.compl₂ (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)).comp
      (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)).compr₂ (-AddMonoidHom.id ℤ))
        (of (M := ℕ) 2 - of 5) (of (M := ℕ) 3) = 36 := by
  rw [lift₂_compr₂, lift₂_comp]
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply,
    AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, map_sub, lift_of, AddMonoidHom.add_apply,
    AddMonoidHom.id_apply, AddMonoidHom.neg_apply, AddMonoidHom.sub_apply, lift₂_of]
  rfl

/-- A signed product formed with the canonical ring's multiplication and casts. -/
private noncomputable def natSignedProduct : Algebra.GrothendieckAddGroup ℕ :=
  (((3 : ℕ) : Algebra.GrothendieckAddGroup ℕ) - ((1 : ℕ) : Algebra.GrothendieckAddGroup ℕ)) *
    (((2 : ℕ) : Algebra.GrothendieckAddGroup ℕ) - ((5 : ℕ) : Algebra.GrothendieckAddGroup ℕ))

/-- The canonical ring's signed product is its integer cast of negative six. -/
private theorem natSignedProduct_eq :
    natSignedProduct = ((-6 : ℤ) : Algebra.GrothendieckAddGroup ℕ) := by
  norm_num [natSignedProduct]

/-- The additive lift supplies an unconditional integer-valued detector. -/
private noncomputable def natIntegerDetector : Algebra.GrothendieckAddGroup ℕ →+ ℤ :=
  lift (Nat.castAddMonoidHom ℤ)

/-- The ring lift retains the whole additive integer-valued detector. -/
private theorem natLiftRingHom_toAddMonoidHom :
    (liftRingHom (Nat.castRingHom ℤ)).toAddMonoidHom = natIntegerDetector := rfl

/-- The ring lift evaluates the canonical signed product as negative six. -/
private theorem natLiftRingHom_signedProduct :
    liftRingHom (Nat.castRingHom ℤ) natSignedProduct = -6 := by
  simp only [natSignedProduct_eq, Int.cast_neg, Int.cast_ofNat, map_neg, map_ofNat]

/-- The signed product is nonzero, detected without identifying the completion with ℤ. -/
private theorem natSignedProduct_ne_zero : natSignedProduct ≠ 0 := by
  intro h
  have hdet := congrArg natIntegerDetector h
  rw [natSignedProduct_eq] at hdet
  change lift (Nat.castAddMonoidHom ℤ) ((-6 : ℤ) • of (M := ℕ) 1) =
    lift (Nat.castAddMonoidHom ℤ) 0 at hdet
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply] at hdet
  rw [map_zsmul, lift_of, map_zero] at hdet
  norm_num at hdet

/-- Every input and product is zero in the canonical commutative ring on the one-element
semiring's completion, and its unit is zero. -/
private theorem punit_ring_boundary (x y : Algebra.GrothendieckAddGroup PUnit.{u + 1}) :
    x = 0 ∧ x * y = 0 ∧ (1 : Algebra.GrothendieckAddGroup PUnit.{u + 1}) = 0 := by
  have h : Subsingleton (Algebra.GrothendieckAddGroup PUnit.{u + 1}) :=
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid PUnit.{u + 1})).subsingleton_of_subsingleton
  exact ⟨h.elim _ _, h.elim _ _, h.elim _ _⟩

end GroupTheoryTest.GrothendieckGroup
