/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.IndexNSmul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic

/-!
# Mixed free and torsion scalar-index examples

Doubling on `ℤ × ZMod 2` has integer finrank one, kernel cardinality two and
index four. Doubling on `ℤ × ZMod 3` is injective despite nonzero finite torsion;
its kernel cardinality is one and its index is two. These examples distinguish
integer module rank from minimum-generator rank and do not assume freeness.
The zero-scalar free example also records the infinite-kernel cardinal convention.
-/

@[expose] public section

namespace GroupTheoryTest.IndexNSmul

example : AddGroup.FG (ℤ × ZMod 2) := inferInstance

example : AddGroup.FG (ℤ × ZMod 3) := inferInstance

/-- A nonzero element of order two in the mixed group. -/
example : ((0, 1) : ℤ × ZMod 2) ≠ 0 ∧ (2 : ℕ) • ((0, 1) : ℤ × ZMod 2) = 0 := by
  decide

private theorem finrank_int_prod_finite (T : Type*) [AddCommGroup T] [Finite T] :
    Module.finrank ℤ (ℤ × T) = 1 := by
  let f : ℤ × T →ₗ[ℤ] ℤ := LinearMap.fst ℤ ℤ T
  have htor : LinearMap.ker f ≤ Submodule.torsion ℤ (ℤ × T) := by
    intro x hx
    change x ∈ (Submodule.torsion ℤ (ℤ × T)).toAddSubgroup
    rw [Submodule.torsion_int, AddCommGroup.mem_torsion, IsOfFinAddOrder.prod_iff]
    have hx0 : x.1 = 0 := hx
    exact ⟨by simp [hx0], isOfFinAddOrder_of_finite x.2⟩
  have hsurj : Function.Surjective f := fun z ↦ ⟨(z, 0), rfl⟩
  rw [← finrank_quotient_eq_of_le_torsion htor,
    (f.quotKerEquivOfSurjective hsurj).finrank_eq]
  exact Module.finrank_self ℤ

private theorem mixed_two_rank_and_kernel :
    Module.finrank ℤ (ℤ × ZMod 2) = 1 ∧
      Nat.card ((nsmulAddMonoidHom (α := ℤ × ZMod 2) 2).ker) = 2 := by
  refine ⟨finrank_int_prod_finite _, ?_⟩
  let e : (nsmulAddMonoidHom (α := ℤ × ZMod 2) 2).ker ≃ ZMod 2 :=
    { toFun := fun x ↦ x.1.2
      invFun := fun x ↦ ⟨(0, x), by
        change (2 : ℕ) • ((0, x) : ℤ × ZMod 2) = 0
        exact Prod.ext (nsmul_zero _) (ZModModule.char_nsmul_eq_zero 2 x)⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        apply Prod.ext
        · apply AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree
            (M := ℤ) (n := 2) (by decide)
          exact (congrArg Prod.fst x.property).symm
        · rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card]

example : (nsmulAddMonoidHom (α := ℤ × ZMod 2) 2).range.index = 4 := by
  rw [AddSubgroup.index_range_nsmul_eq_mul_natCard_ker,
    mixed_two_rank_and_kernel.1, mixed_two_rank_and_kernel.2]
  norm_num

/-- A nonzero element of order three, compatible with injective doubling. -/
example : ((0, 1) : ℤ × ZMod 3) ≠ 0 ∧ (3 : ℕ) • ((0, 1) : ℤ × ZMod 3) = 0 := by
  decide

private theorem mixed_three_two_injective :
    Function.Injective (nsmulAddMonoidHom (α := ℤ × ZMod 3) 2) := by
  intro x y h
  apply Prod.ext
  · exact AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree
      (M := ℤ) (n := 2) (by decide) (congrArg Prod.fst h)
  · have hcoprime : Nat.Coprime (Nat.card (ZMod 3)) 2 := by
      norm_num [Nat.card_eq_fintype_card, ZMod.card]
      decide
    exact (Nat.Coprime.nsmul_right_bijective hcoprime).injective (congrArg Prod.snd h)

private theorem mixed_three_rank_and_kernel :
    Module.finrank ℤ (ℤ × ZMod 3) = 1 ∧
      Nat.card ((nsmulAddMonoidHom (α := ℤ × ZMod 3) 2).ker) = 1 := by
  refine ⟨finrank_int_prod_finite _, ?_⟩
  rw [(nsmulAddMonoidHom (α := ℤ × ZMod 3) 2).ker_eq_bot mixed_three_two_injective]
  simp

example : (nsmulAddMonoidHom (α := ℤ × ZMod 3) 2).range.index = 2 := by
  rw [AddSubgroup.index_range_nsmul_of_injective _ _ mixed_three_two_injective,
    mixed_three_rank_and_kernel.1]
  norm_num

/-- At zero on `ℤ`, the infinite kernel has natural cardinality zero. -/
example : Nat.card ((nsmulAddMonoidHom (α := ℤ) 0).ker) = 0 := by
  have hker : (nsmulAddMonoidHom (α := ℤ) 0).ker = ⊤ := by
    ext x
    simp
  rw [hker, Nat.card_congr AddSubgroup.topEquiv.toEquiv]
  exact Nat.card_eq_zero_of_infinite

example : (0 : ℕ) ^ Module.finrank ℤ ℤ *
    Nat.card ((nsmulAddMonoidHom (α := ℤ) 0).ker) = 0 := by
  rw [AddSubgroup.pow_finrank_mul_natCard_ker_nsmul_eq_pow_finrank]
  norm_num

end GroupTheoryTest.IndexNSmul
