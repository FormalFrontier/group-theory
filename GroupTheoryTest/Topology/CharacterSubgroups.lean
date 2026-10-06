/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CharacterSubgroups
public import GroupTheoryTest.Topology.FiniteIndex
public import Mathlib.Topology.Instances.ZMod

/-!
# Nontrivial rational-circle characters on finite and 2-adic groups

The nonzero character on `ZMod 2` sends its generator to the rational half-circle.
Restriction along reduction modulo two gives an open-kernel character of the infinite
compact additive group of 2-adic integers. The open range of the doubling map
supplies an independent way to see that its kernel is open.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.CharacterSubgroups

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The character on the two-element additive group with generator value `1/2`. -/
noncomputable def twoCharacter : CharacterModule (ZMod 2) :=
  ZMod.lift 2 ⟨AddMonoidHom.mk' (fun integer : ℤ =>
      integer • (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ))) (by
        intro left right
        exact add_zsmul _ left right),
    by
      have horder :
          addOrderOf (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) = 2 :=
        AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (by norm_num)
      change (2 : ℕ) • (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) = 0
      simpa only [horder] using
        (addOrderOf_nsmul_eq_zero (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)))⟩

/-- The generator has the desired, nonzero rational-circle value. -/
theorem twoCharacter_one :
    twoCharacter (1 : ZMod 2) = (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
  unfold twoCharacter
  erw [ZMod.lift_coe]
  change (1 : ℤ) • (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) = _
  exact one_zsmul _

/-- The two-element character is nonzero and has an open proper kernel. -/
theorem twoCharacter_openKernel_nontrivial :
    twoCharacter ∈ CharacterModule.openKernel (ZMod 2) ∧
      (1 : ZMod 2) ∉ twoCharacter.ker := by
  constructor
  · exact (CharacterModule.mem_openKernel twoCharacter).2 (isOpen_discrete _)
  · intro hmem
    have hzero : twoCharacter (1 : ZMod 2) = 0 := hmem
    rw [twoCharacter_one] at hzero
    have horder :
        addOrderOf (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) = 2 :=
      AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (by norm_num)
    rw [hzero] at horder
    norm_num at horder

/-- The finite example also exercises the finite-image characterization. -/
theorem twoCharacter_torsion_and_finite_range :
    twoCharacter ∈ AddCommGroup.torsion (CharacterModule (ZMod 2)) ∧
      (Set.range twoCharacter).Finite ∧ twoCharacter (1 : ZMod 2) ≠ 0 := by
  have hfinite : (Set.range twoCharacter).Finite := Set.finite_range _
  exact ⟨(CharacterModule.mem_torsion_iff_finite_range twoCharacter).2 hfinite,
    hfinite, fun h => twoCharacter_openKernel_nontrivial.2 (by
      change twoCharacter (1 : ZMod 2) = 0
      exact h)⟩

/-- Reduction modulo two viewed as a continuous additive homomorphism. -/
noncomputable def padicReduction : ℤ_[2] →ₜ+ ZMod 2 where
  toAddMonoidHom := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom
  continuous_toFun := by
    have hker : IsOpen
        (((PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom).ker : Set ℤ_[2]) := by
      apply AddSubgroup.isOpen_mono
        (H₁ := (nsmulAddMonoidHom (α := ℤ_[2]) 2).range)
      · rintro _ ⟨element, rfl⟩
        change (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) (2 • element) = 0
        rw [map_nsmul]
        exact ZModModule.char_nsmul_eq_zero 2 _
      · exact GroupTheoryTest.Topology.FiniteIndex.two_nsmul_range_finiteIndex_and_open.2
    exact (((PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom).isLocallyConstant_of_isOpen_ker
      hker).continuous

/-- The 2-adic character obtained by restricting the finite character. -/
noncomputable def padicCharacter : CharacterModule.openKernel ℤ_[2] :=
  CharacterModule.openKernelRestrict padicReduction
    ⟨twoCharacter, twoCharacter_openKernel_nontrivial.1⟩

/-- The restricted character remains nontrivial on the 2-adic unit and has an open,
proper kernel. -/
theorem padicCharacter_openKernel_nontrivial :
    (padicCharacter : CharacterModule ℤ_[2]) ∈ CharacterModule.openKernel ℤ_[2] ∧
      (1 : ℤ_[2]) ∉ (padicCharacter : CharacterModule ℤ_[2]).ker ∧
      (padicCharacter : CharacterModule ℤ_[2]) 1 =
        (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) := by
  have hone : (padicReduction (1 : ℤ_[2])) = (1 : ZMod 2) := by
    change (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 1 = 1
    exact map_one _
  have hvalue : (padicCharacter : CharacterModule ℤ_[2]) 1 =
      (↑((1 : ℚ) / 2) : AddCircle (1 : ℚ)) := by
    simp [padicCharacter, hone, twoCharacter_one]
  refine ⟨padicCharacter.property, ?_, hvalue⟩
  intro hmem
  have hzero : (padicCharacter : CharacterModule ℤ_[2]) 1 = 0 := hmem
  rw [hvalue] at hzero
  exact twoCharacter_openKernel_nontrivial.2 (by
    change twoCharacter (1 : ZMod 2) = 0
    simpa only [twoCharacter_one] using hzero)

/-- Both character restrictions preserve a nonzero value on the 2-adic unit. -/
theorem padicCharacter_torsion_restrict_nontrivial :
    ((CharacterModule.torsionRestrict padicReduction.toAddMonoidHom
      ⟨twoCharacter, twoCharacter_torsion_and_finite_range.1⟩ :
        CharacterModule ℤ_[2]) (1 : ℤ_[2])) ≠ 0 := by
  change twoCharacter (padicReduction (1 : ℤ_[2])) ≠ 0
  have hone : padicReduction (1 : ℤ_[2]) = (1 : ZMod 2) := by
    change (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 1 = 1
    exact map_one _
  rw [hone]
  exact twoCharacter_torsion_and_finite_range.2.2

/-- In the finite example, the dense finitely generated subgroup can be the whole group;
the equality compares two subgroups containing a nonzero character. -/
theorem twoCharacter_dense_fg_comparison :
    twoCharacter ∈ CharacterModule.openKernel (ZMod 2) ⊓
      AddCommGroup.torsion (CharacterModule (ZMod 2)) ∧
      twoCharacter (1 : ZMod 2) ≠ 0 := by
  have hfg : (⊤ : AddSubgroup (ZMod 2)).FG :=
    (AddGroup.fg_iff_addSubgroup_fg ⊤).mp
      (inferInstance : AddGroup.FG (⊤ : AddSubgroup (ZMod 2)))
  have hdense : Dense ((⊤ : AddSubgroup (ZMod 2)) : Set (ZMod 2)) := by
    simpa only [AddSubgroup.coe_top] using (dense_univ : Dense (Set.univ : Set (ZMod 2)))
  have heq := CharacterModule.openKernel_eq_torsion_of_dense_fg
    (⊤ : AddSubgroup (ZMod 2)) hfg hdense
  have hmem := twoCharacter_openKernel_nontrivial.1
  have htorsion : twoCharacter ∈ AddCommGroup.torsion (CharacterModule (ZMod 2)) := by
    rw [← heq]
    exact hmem
  exact ⟨⟨hmem, htorsion⟩, twoCharacter_torsion_and_finite_range.2.2⟩

/-- On the infinite compact domain, the open-kernel inclusion applies to a character
with a proper kernel. -/
theorem padicCharacter_compact_comparison :
    (padicCharacter : CharacterModule ℤ_[2]) ∈
      AddCommGroup.torsion (CharacterModule ℤ_[2]) ∧
      (1 : ℤ_[2]) ∉ (padicCharacter : CharacterModule ℤ_[2]).ker := by
  exact ⟨CharacterModule.openKernel_le_torsion padicCharacter.property,
    padicCharacter_openKernel_nontrivial.2.1⟩

section NonHausdorff

local instance : TopologicalSpace (ZMod 2) := ⊤
local instance : IndiscreteTopology (ZMod 2) := ⟨rfl⟩

/-- A finite-image character of the compact indiscrete two-element group can have
a non-open kernel, so Hausdorffness matters in the converse comparison. -/
theorem twoCharacter_not_openKernel_indiscrete :
    twoCharacter ∉ CharacterModule.openKernel (ZMod 2) := by
  intro hmem
  have hopen := (CharacterModule.mem_openKernel twoCharacter).mp hmem
  rcases (IndiscreteTopology.isOpen_iff _).mp hopen with hempty | huniv
  · have hzero : (0 : ZMod 2) ∈ (twoCharacter.ker : Set (ZMod 2)) := by simp
    simp [hempty] at hzero
  · apply twoCharacter_openKernel_nontrivial.2
    change (1 : ZMod 2) ∈ (twoCharacter.ker : Set (ZMod 2))
    rw [huniv]
    exact Set.mem_univ _

end NonHausdorff

end GroupTheoryTest.Topology.CharacterSubgroups

end
