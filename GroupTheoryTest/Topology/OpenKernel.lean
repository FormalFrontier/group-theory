/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CircleCharacter
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Topology.Instances.ZMod

/-!
# Examples of finite-image circle characters

The standard character of the two-element cyclic group has nontrivial finite image.
Its factorization through its kernel does not assert surjectivity onto the circle.
-/

@[expose] public section

open Filter
open scoped Topology

namespace GroupTheoryTest.Topology.OpenKernel

private instance : NonarchimedeanGroup (Multiplicative (ZMod 2)) where
  is_nonarchimedean U hU := by
    let H : OpenSubgroup (Multiplicative (ZMod 2)) :=
      { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
    refine ⟨H, ?_⟩
    intro g hg
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    rw [hg1]
    exact mem_of_mem_nhds hU

/-- The standard character on a cyclic group of order two, regarded as a
continuous homomorphism into the circle. -/
noncomputable def twoCharacter : Multiplicative (ZMod 2) →ₜ* Circle where
  toMonoidHom := (ZMod.toCircle (N := 2)).toMonoidHom
  continuous_toFun := continuous_of_discreteTopology

/-- The value of the character on the nonidentity element is not the identity. -/
theorem twoCharacter_nontrivial :
    twoCharacter (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
  intro h
  change ZMod.toCircle (1 : ZMod 2) = 1 at h
  have heq : ZMod.toCircle (1 : ZMod 2) = ZMod.toCircle (0 : ZMod 2) := by
    simpa using h
  have hone : (1 : ZMod 2) = 0 := ZMod.injective_toCircle heq
  norm_num at hone

/-- A nonconstant finite character gives a nontrivial image and a finite
quotient by its actual kernel. -/
theorem twoCharacter_finite_nontrivial :
    IsLocallyConstant (twoCharacter : Multiplicative (ZMod 2) → Circle) ∧
      (Set.range twoCharacter).Finite ∧
      twoCharacter (Multiplicative.ofAdd (1 : ZMod 2)) ≠ twoCharacter 1 ∧
      Finite (Multiplicative (ZMod 2) ⧸ twoCharacter.toMonoidHom.ker) ∧
      DiscreteTopology (Multiplicative (ZMod 2) ⧸ twoCharacter.toMonoidHom.ker) ∧
      QuotientGroup.kerLift twoCharacter.toMonoidHom
        (QuotientGroup.mk (Multiplicative.ofAdd (1 : ZMod 2))) ≠ 1 := by
  refine ⟨twoCharacter.toMonoidHom.isLocallyConstant_of_isOpen_ker
    (Circle.isOpen_ker twoCharacter), Circle.finite_range twoCharacter, ?_, ?_, ?_, ?_⟩
  · simpa using twoCharacter_nontrivial
  · exact (twoCharacter.finite_quotient_kerLift _
      Circle.centeredArc_pi_div_two_mem_nhds_one
      Circle.subgroup_eq_bot_of_subset_centeredArc_pi_div_two).1
  · exact (twoCharacter.finite_quotient_kerLift _
      Circle.centeredArc_pi_div_two_mem_nhds_one
      Circle.subgroup_eq_bot_of_subset_centeredArc_pi_div_two).2.1
  · rw [QuotientGroup.kerLift_mk]
    change twoCharacter (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1
    exact twoCharacter_nontrivial

end GroupTheoryTest.Topology.OpenKernel

end
