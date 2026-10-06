/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex
public import GroupTheoryTest.Topology.PadicDenseIntegers
import Mathlib.Algebra.CharZero.Infinite

/-!
# Dense finite generation and open finite-index subgroups

The embedded integers generate a dense additive subgroup of the compact 2-adic
integers. Reduction modulo two gives a proper finite-index subgroup; the open
subgroup result applies without supplying a closedness hypothesis. This example
does not assume that the whole additive group of 2-adic integers is abstractly
finitely generated.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.FiniteIndex

open GroupTheoryTest.Topology.PadicDenseIntegers

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private noncomputable def parityKernel : AddSubgroup ℤ_[2] :=
  (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom.ker

/-- Doubling in the 2-adic integers has finite-index open image, witnessed by a
dense copy of the finitely generated additive group of integers. -/
theorem two_nsmul_range_finiteIndex_and_open :
    (nsmulAddMonoidHom (α := ℤ_[2]) 2).range.FiniteIndex ∧
      IsOpen ((nsmulAddMonoidHom (α := ℤ_[2]) 2).range : Set ℤ_[2]) := by
  exact ⟨AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_dense_fg
    padicIntegers padicIntegers_fg padicIntegers_dense (by norm_num),
    AddSubgroup.isOpen_range_nsmulAddMonoidHom_of_dense_fg
      padicIntegers padicIntegers_fg padicIntegers_dense (by norm_num)⟩

/-- The 2-adic integers have a proper open additive subgroup given by reduction modulo two. -/
private theorem parityKernel_open_and_proper : IsOpen (parityKernel : Set ℤ_[2]) ∧
    parityKernel ≠ ⊤ := by
  have hsurj : Function.Surjective (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) :=
    ZMod.ringHom_surjective _
  have hfinite : parityKernel.FiniteIndex := by
    dsimp [parityKernel]
    infer_instance
  constructor
  · exact @AddSubgroup.isOpen_of_finiteIndex_of_dense_fg ℤ_[2] _ _ _ _ _
      padicIntegers padicIntegers_fg padicIntegers_dense parityKernel hfinite
  · intro htop
    obtain ⟨element, helement⟩ := hsurj (1 : ZMod 2)
    have hmem : element ∈ parityKernel := by rw [htop]; exact AddSubgroup.mem_top _
    have hzero : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) element = 0 := by
      change ((PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom element) = 0 at hmem
      exact hmem
    exact one_ne_zero (helement.symm.trans hzero)

/-- The positivity assumption on the exponent cannot be removed for the infinite
compact group of 2-adic integers: the zero scalar map has infinite index. -/
theorem zero_nsmul_range_not_finiteIndex :
    ¬ (nsmulAddMonoidHom (α := ℤ_[2]) 0).range.FiniteIndex := by
  have hrange : (nsmulAddMonoidHom (α := ℤ_[2]) 0).range =
      (⊥ : AddSubgroup ℤ_[2]) := by
    ext element
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, zero_nsmul,
      exists_const, AddSubgroup.mem_bot]
    exact eq_comm
  rw [hrange, AddSubgroup.not_finiteIndex_iff, AddSubgroup.index_bot,
    Nat.card_eq_zero_of_infinite]

end GroupTheoryTest.Topology.FiniteIndex

end
