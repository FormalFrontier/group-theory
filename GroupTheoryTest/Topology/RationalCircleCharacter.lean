/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.RationalCircleCharacter
public import GroupTheoryTest.Topology.CharacterSubgroups
public import GroupTheoryTest.Topology.PadicDenseIntegers
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Rational and circle characters on the two-element and 2-adic groups

The rational half-circle character on `ZMod 2` produces a nontrivial
continuous circle character. Reduction modulo two pulls it back to the
compact, infinite additive group of 2-adic integers. The comparison maps
have the same nonzero evaluation and commute with this reduction.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.RationalCircleCharacter

open GroupTheoryTest.Topology.CharacterSubgroups
open GroupTheoryTest.Topology.PadicDenseIntegers

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The discrete two-element group has an open-subgroup basis. -/
instance : NonarchimedeanAddGroup (ZMod 2) where
  is_nonarchimedean U hU := by
    refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
    intro value hvalue
    have hzero : value = 0 := hvalue
    simpa [hzero] using mem_of_mem_nhds hU

/-- The rational half-circle character, regarded as an open-kernel character. -/
noncomputable def finiteOpenCharacter : CharacterModule.openKernel (ZMod 2) :=
  ⟨twoCharacter, twoCharacter_openKernel_nontrivial.1⟩

/-- The rational half-circle maps to a nonidentity point on the unit circle. -/
theorem halfCircle_ne_one :
    Additive.toMul (AddCircle.rationalToCircle
      (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) ≠ 1 := by
  intro h
  have h' : Additive.toMul (AddCircle.rationalToCircle
      (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) =
      Additive.toMul (AddCircle.rationalToCircle 0) := by
    simpa only [map_zero, toMul_zero] using h
  have heq : AddCircle.rationalToCircle
      (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) =
      AddCircle.rationalToCircle 0 := by
    simpa only [ofMul_toMul] using congrArg Additive.ofMul h'
  have hzero := AddCircle.rationalToCircle_injective heq
  exact twoCharacter_torsion_and_finite_range.2.2 (by
    simpa only [twoCharacter_one] using hzero)

/-- The forward construction preserves the nonzero half-circle value. -/
theorem finite_forward_value :
    Additive.toMul (CharacterModule.openKernelToPontryagin finiteOpenCharacter)
        (Multiplicative.ofAdd (1 : ZMod 2)) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  simp [finiteOpenCharacter, twoCharacter_one]

/-- The forward character is nontrivial already on the finite boundary example. -/
theorem finite_forward_nontrivial :
    Additive.toMul (CharacterModule.openKernelToPontryagin finiteOpenCharacter)
        (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
  rw [finite_forward_value]
  exact halfCircle_ne_one

/-- The 2-adic reduction character has the same half-circle evaluation. -/
theorem padic_forward_value :
    Additive.toMul (CharacterModule.openKernelToPontryagin padicCharacter)
        (Multiplicative.ofAdd (1 : ℤ_[2])) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  simp [padicCharacter_openKernel_nontrivial.2.2]

/-- The circle character from 2-adic reduction really is nontrivial. -/
theorem padic_forward_nontrivial :
    Additive.toMul (CharacterModule.openKernelToPontryagin padicCharacter)
        (Multiplicative.ofAdd (1 : ℤ_[2])) ≠ 1 := by
  rw [padic_forward_value]
  exact halfCircle_ne_one

/-- The full two-element group is finitely generated. -/
theorem finiteWhole_fg : (⊤ : AddSubgroup (ZMod 2)).FG :=
  (AddGroup.fg_iff_addSubgroup_fg ⊤).mp
    (inferInstance : AddGroup.FG (⊤ : AddSubgroup (ZMod 2)))

/-- The full two-element group is dense in itself. -/
theorem finiteWhole_dense :
    Dense ((⊤ : AddSubgroup (ZMod 2)) : Set (ZMod 2)) := by
  simpa only [AddSubgroup.coe_top] using (dense_univ : Dense (Set.univ : Set (ZMod 2)))

/-- The finite-order comparison retains the concrete half-circle evaluation. -/
theorem finite_order_equivalence_value :
    Additive.toMul (CharacterModule.torsionEquivPontryaginOfDenseFG
        (⊤ : AddSubgroup (ZMod 2)) finiteWhole_fg finiteWhole_dense
        ⟨twoCharacter, twoCharacter_torsion_and_finite_range.1⟩)
        (Multiplicative.ofAdd (1 : ZMod 2)) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  simp [twoCharacter_one]

/-- In particular, the finite-order comparison is nontrivial on its generator. -/
theorem finite_order_equivalence_nontrivial :
    Additive.toMul (CharacterModule.torsionEquivPontryaginOfDenseFG
        (⊤ : AddSubgroup (ZMod 2)) finiteWhole_fg finiteWhole_dense
        ⟨twoCharacter, twoCharacter_torsion_and_finite_range.1⟩)
        (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
  rw [finite_order_equivalence_value]
  exact halfCircle_ne_one

/-- The inverse finite-order comparison recovers the same nonzero generator value. -/
theorem finite_order_inverse_value :
    Additive.toMul (AddCircle.rationalToCircle
      (((CharacterModule.torsionEquivPontryaginOfDenseFG
          (⊤ : AddSubgroup (ZMod 2)) finiteWhole_fg finiteWhole_dense).symm
          (CharacterModule.openKernelToPontryagin finiteOpenCharacter)).1 (1 : ZMod 2))) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  rw [CharacterModule.torsionEquivPontryaginOfDenseFG_symm_apply,
    finite_forward_value]

/-- The nonzero 2-adic character has finite order. -/
noncomputable def padicTorsionCharacter : AddCommGroup.torsion (CharacterModule ℤ_[2]) :=
  ⟨padicCharacter.1, CharacterModule.openKernel_le_torsion padicCharacter.property⟩

/-- The finite-order comparison also detects the half-circle on the infinite
compact 2-adic group, with the dense embedded integers as its generators. -/
theorem padic_finite_order_value :
    Additive.toMul (CharacterModule.torsionEquivPontryaginOfDenseFG
        padicIntegers padicIntegers_fg padicIntegers_dense padicTorsionCharacter)
        (Multiplicative.ofAdd (1 : ℤ_[2])) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  simp [padicTorsionCharacter, padicCharacter_openKernel_nontrivial.2.2]

/-- The finite-order image of the 2-adic character is nontrivial. -/
theorem padic_finite_order_nontrivial :
    Additive.toMul (CharacterModule.torsionEquivPontryaginOfDenseFG
        padicIntegers padicIntegers_fg padicIntegers_dense padicTorsionCharacter)
        (Multiplicative.ofAdd (1 : ℤ_[2])) ≠ 1 := by
  rw [padic_finite_order_value]
  exact halfCircle_ne_one

/-- Pulling back the finite forward character via the Pontryagin dual agrees
with applying the forward construction after rational-circle restriction. -/
theorem padic_naturality :
    CharacterModule.openKernelToPontryagin padicCharacter =
      Additive.ofMul (PontryaginDual.map padicReduction.toMultiplicative
        (Additive.toMul (CharacterModule.openKernelToPontryagin finiteOpenCharacter))) := by
  exact CharacterModule.openKernelToPontryagin_naturality
    padicReduction finiteOpenCharacter

/-- Finite-order inversion commutes with reduction from the 2-adic integers. -/
theorem padic_finite_order_inverse_restrict :
    CharacterModule.torsionRestrict padicReduction.toAddMonoidHom
      ((CharacterModule.torsionEquivPontryaginOfDenseFG
        (⊤ : AddSubgroup (ZMod 2)) finiteWhole_fg finiteWhole_dense).symm
        (CharacterModule.openKernelToPontryagin finiteOpenCharacter)) =
      (CharacterModule.torsionEquivPontryaginOfDenseFG
        padicIntegers padicIntegers_fg padicIntegers_dense).symm
        (CharacterModule.openKernelToPontryagin padicCharacter) := by
  rw [CharacterModule.torsionEquivPontryaginOfDenseFG_symm_naturality,
    ← padic_naturality]

/-- Tag transport agrees with dual precomposition by the identity on `ZMod 2`. -/
theorem finite_dual_map_id
    (χ : PontryaginDual (Multiplicative (ZMod 2))) :
    PontryaginDual.map
        ((ContinuousAddMonoidHom.id (ZMod 2)).toMultiplicative) χ = χ := by
  rw [ContinuousAddMonoidHom.toMultiplicative_id]
  apply PontryaginDual.ext
  intro value
  rfl

/-- Tag transport preserves the composition in dual reduction. -/
theorem padic_dual_map_comp
    (χ : PontryaginDual (Multiplicative (ZMod 2))) :
    PontryaginDual.map
        (((ContinuousAddMonoidHom.id (ZMod 2)).comp padicReduction).toMultiplicative) χ =
      PontryaginDual.map padicReduction.toMultiplicative
        (PontryaginDual.map
          ((ContinuousAddMonoidHom.id (ZMod 2)).toMultiplicative) χ) := by
  rw [ContinuousAddMonoidHom.toMultiplicative_comp, PontryaginDual.map_comp]
  rfl

/-- Inverting the comparison recovers the 2-adic character's half-circle value. -/
theorem padic_inverse_value :
    Additive.toMul (AddCircle.rationalToCircle
      (((CharacterModule.openKernelEquivPontryagin (A := ℤ_[2])).symm
        (CharacterModule.openKernelToPontryagin padicCharacter)).1 (1 : ℤ_[2]))) =
      Additive.toMul (AddCircle.rationalToCircle
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) := by
  rw [CharacterModule.openKernelEquivPontryagin_symm_apply, padic_forward_value]

end GroupTheoryTest.Topology.RationalCircleCharacter

end
