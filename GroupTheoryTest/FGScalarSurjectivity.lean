/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.FGScalarSurjectivity
public import Mathlib.Logic.Function.Defs
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

namespace GroupTheoryTest.FGScalarSurjectivity

example {A : Type*} [AddCommGroup A] [AddGroup.FG A] {n : ℕ}
    (hn : 2 ≤ n) (hsurj : Function.Surjective (fun x : A => n • x)) :
    Finite A ∧ Nat.Coprime n (Nat.card A) :=
  AddCommGroup.finite_coprime_of_nsmul_surjective hn hsurj

example {A : Type*} [AddCommGroup A] [AddGroup.FG A] {n : ℕ}
    (hn : 2 ≤ n) (hsurj : Function.Surjective (fun x : A => n • x)) :
    Function.Bijective (fun x : A => n • x) := by
  obtain ⟨k, hright, hleft⟩ :=
    AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective hn hsurj
  constructor
  · intro x y heq
    calc
      x = k • (n • x) := (hleft x).symm
      _ = k • (n • y) := congrArg (k • ·) heq
      _ = y := hleft y
  · intro y
    exact ⟨k • y, hright y⟩

example : Function.Surjective (fun x : ZMod 1 => (2 : ℕ) • x) := by
  apply (AddCommGroup.nsmul_surjective_iff_finite_coprime
    (A := ZMod 1) (n := 2) (by decide)).mpr
  constructor
  · infer_instance
  · norm_num [Nat.card_eq_fintype_card, ZMod.card]

example : (1 : ZMod 7) ≠ 0 := by decide

/-- Multiplication by two is bijective on `ZMod 7`. -/
theorem zmod_seven_two_nsmul_bijective :
    Function.Bijective (fun x : ZMod 7 => (2 : ℕ) • x) := by
  apply (AddCommGroup.nsmul_bijective_iff_finite_coprime
    (A := ZMod 7) (n := 2) (by decide)).mpr
  constructor
  · infer_instance
  · norm_num [Nat.card_eq_fintype_card, ZMod.card]
    decide

end GroupTheoryTest.FGScalarSurjectivity

end
