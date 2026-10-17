/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic

/-!
# Integer-valued Grothendieck lifts

The additive lift of the canonical map from natural numbers to integers sends a difference
of generators to a negative integer. Extending natural-number multiplication in both
variables gives the corresponding negative product on a difference of generators.
These examples use the completion's canonical generators without identifying the
completion with another model.
-/

@[expose] public section

namespace GroupTheoryTest.GrothendieckGroup

open Algebra.GrothendieckAddGroup

/-- The additive extension of the natural-number cast evaluates a negative difference. -/
example : liftAddEquiv (Nat.castAddMonoidHom ℤ) (of (M := ℕ) 2 - of 5) = -3 := by
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
  rw [map_sub, AddMonoidHom.sub_apply, lift₂_of, lift₂_of]
  rfl

/-- Doubling both inputs and negating the output commutes with bilinear extension,
even on a difference of generators. -/
example :
    lift₂ (((natMulInt.compl₂ (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)).comp
      (AddMonoidHom.id ℕ + AddMonoidHom.id ℕ)).compr₂ (-AddMonoidHom.id ℤ))
        (of (M := ℕ) 2 - of 5) (of (M := ℕ) 3) = 36 := by
  rw [lift₂_compr₂, lift₂_comp]
  simp only [AddMonoidHom.compr₂_apply, AddMonoidHom.compl₂_apply,
    AddMonoidHom.comp_apply, map_sub, lift_of, AddMonoidHom.add_apply,
    AddMonoidHom.id_apply, AddMonoidHom.neg_apply, AddMonoidHom.sub_apply, lift₂_of]
  rfl

end GroupTheoryTest.GrothendieckGroup
