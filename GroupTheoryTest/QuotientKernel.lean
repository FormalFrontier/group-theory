/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.QuotientGroup.Kernel
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A diagonal map on the rational plane modulo the integer lattice

The diagonal additive equivalence `(x, y) ↦ (2 * x, 3 * y)` preserves
`ℤ × ℤ` inside `ℚ × ℚ`. Its induced endomorphism of the quotient kills the
nonzero classes of `(1 / 2, 0)` and `(0, 1 / 3)`. The two integer basis vectors
have nonzero classes modulo the image lattice. All four classes and their
nonvanishing are constructed directly from the coordinate formulas.

The quotient-kernel equivalence sends these two kernel classes to the classes
of `(1, 0)` and `(0, 1)`, respectively, and its inverse recovers the displayed
rational representatives. The diagonal equivalence is a product of Mathlib's
scalar linear equivalences, but is not multiplication by a common scalar.
-/

@[expose] public section

namespace QuotientAddGroup

/-- The product of the integer subgroups of the two rational coordinates. -/
private def integerLattice : AddSubgroup (ℚ × ℚ) :=
  (AddSubgroup.zmultiples (1 : ℚ)).prod (AddSubgroup.zmultiples (1 : ℚ))

/-- The diagonal equivalence with distinct multipliers on the two coordinates. -/
private def diagonal : (ℚ × ℚ) ≃+ (ℚ × ℚ) :=
  ((LinearEquiv.smulOfNeZero ℚ ℚ 2 (by norm_num)).prodCongr
    (LinearEquiv.smulOfNeZero ℚ ℚ 3 (by norm_num))).toAddEquiv

private theorem diagonal_apply (p : ℚ × ℚ) : diagonal p = (2 * p.1, 3 * p.2) :=
  rfl

private theorem diagonal_symm_apply (p : ℚ × ℚ) :
    diagonal.symm p = (p.1 / 2, p.2 / 3) := by
  apply diagonal.injective
  rw [diagonal.apply_symm_apply, diagonal_apply]
  ext <;> dsimp <;> ring

private theorem diagonal_not_scalar :
    ¬ ∃ c : ℚ, ∀ p : ℚ × ℚ, diagonal p = c • p := by
  rintro ⟨c, hc⟩
  have h₂ := congrArg Prod.fst (hc (1, 0))
  have h₃ := congrArg Prod.snd (hc (0, 1))
  norm_num [diagonal_apply] at h₂ h₃
  have h : (2 : ℚ) = 3 := h₂.trans h₃.symm
  norm_num at h

/-- Multiplication by two and three sends integer coordinates to integer coordinates. -/
private theorem diagonal_preserves :
    integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ)) ≤ integerLattice := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (AddSubgroup.mem_prod.mp hp).1
  obtain ⟨b, hb⟩ := AddSubgroup.mem_zmultiples_iff.mp (AddSubgroup.mem_prod.mp hp).2
  change (2 * p.1, 3 * p.2) ∈ integerLattice
  refine AddSubgroup.mem_prod.mpr ⟨?_, ?_⟩
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨2 * a, ?_⟩
    simpa only [zsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat] using
      congrArg (fun q : ℚ => 2 * q) ha
  · refine AddSubgroup.mem_zmultiples_iff.mpr ⟨3 * b, ?_⟩
    simpa only [zsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat] using
      congrArg (fun q : ℚ => 3 * q) hb

/-- The endomorphism induced by the diagonal equivalence on the quotient plane. -/
private def diagonalQuotient : ((ℚ × ℚ) ⧸ integerLattice) →+
    ((ℚ × ℚ) ⧸ integerLattice) :=
  map integerLattice integerLattice (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ))
    (AddSubgroup.map_le_iff_le_comap.mp diagonal_preserves)

private def firstBasis : integerLattice :=
  ⟨(1, 0), AddSubgroup.mem_prod.mpr
    ⟨AddSubgroup.mem_zmultiples (1 : ℚ), (AddSubgroup.zmultiples (1 : ℚ)).zero_mem⟩⟩

private def secondBasis : integerLattice :=
  ⟨(0, 1), AddSubgroup.mem_prod.mpr
    ⟨(AddSubgroup.zmultiples (1 : ℚ)).zero_mem, AddSubgroup.mem_zmultiples (1 : ℚ)⟩⟩

private theorem diagonal_half_first :
    diagonal ((1 / 2, 0) : ℚ × ℚ) = (firstBasis : ℚ × ℚ) := by
  norm_num [diagonal_apply, firstBasis]

private theorem diagonal_third_second :
    diagonal ((0, 1 / 3) : ℚ × ℚ) = (secondBasis : ℚ × ℚ) := by
  norm_num [diagonal_apply, secondBasis]

private theorem diagonal_symm_first :
    diagonal.symm (firstBasis : ℚ × ℚ) = ((1 / 2, 0) : ℚ × ℚ) := by
  norm_num [diagonal_symm_apply, firstBasis]

private theorem diagonal_symm_second :
    diagonal.symm (secondBasis : ℚ × ℚ) = ((0, 1 / 3) : ℚ × ℚ) := by
  norm_num [diagonal_symm_apply, secondBasis]

/-- The half-class in the first coordinate, constructed in the induced map's kernel. -/
private def halfClass : diagonalQuotient.ker :=
  ⟨(((1 / 2, 0) : ℚ × ℚ) : (ℚ × ℚ) ⧸ integerLattice), by
    change diagonalQuotient _ = 0
    rw [diagonalQuotient, map_mk]
    change ((diagonal ((1 / 2, 0) : ℚ × ℚ) : ℚ × ℚ) :
      (ℚ × ℚ) ⧸ integerLattice) = 0
    rw [diagonal_half_first]
    exact (eq_zero_iff (firstBasis : ℚ × ℚ)).mpr firstBasis.property⟩

/-- The third-class in the second coordinate, constructed in the induced map's kernel. -/
private def thirdClass : diagonalQuotient.ker :=
  ⟨(((0, 1 / 3) : ℚ × ℚ) : (ℚ × ℚ) ⧸ integerLattice), by
    change diagonalQuotient _ = 0
    rw [diagonalQuotient, map_mk]
    change ((diagonal ((0, 1 / 3) : ℚ × ℚ) : ℚ × ℚ) :
      (ℚ × ℚ) ⧸ integerLattice) = 0
    rw [diagonal_third_second]
    exact (eq_zero_iff (secondBasis : ℚ × ℚ)).mpr secondBasis.property⟩

/-- The first integer basis class modulo the diagonal image of the integer lattice. -/
private def firstImageClass :
    integerLattice ⧸
      (integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ))).addSubgroupOf integerLattice :=
  (firstBasis : integerLattice ⧸
    (integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ))).addSubgroupOf integerLattice)

/-- The second integer basis class modulo the diagonal image of the integer lattice. -/
private def secondImageClass :
    integerLattice ⧸
      (integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ))).addSubgroupOf integerLattice :=
  (secondBasis : integerLattice ⧸
    (integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ))).addSubgroupOf integerLattice)

private theorem half_not_integer : (1 / 2 : ℚ) ∉ AddSubgroup.zmultiples (1 : ℚ) := by
  intro h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  have hz' : (z : ℚ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hz
  have hden := congrArg Rat.den hz'
  rw [Rat.div_def', Rat.den_divInt] at hden
  norm_num at hden

private theorem third_not_integer : (1 / 3 : ℚ) ∉ AddSubgroup.zmultiples (1 : ℚ) := by
  intro h
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  have hz' : (z : ℚ) = 1 / 3 := by simpa only [zsmul_eq_mul, mul_one] using hz
  have hden := congrArg Rat.den hz'
  rw [Rat.div_def', Rat.den_divInt] at hden
  norm_num at hden

private theorem halfClass_ne_zero : (halfClass : (ℚ × ℚ) ⧸ integerLattice) ≠ 0 := by
  intro h
  have hmem := (eq_zero_iff ((1 / 2, 0) : ℚ × ℚ)).mp h
  exact half_not_integer (AddSubgroup.mem_prod.mp hmem).1

private theorem thirdClass_ne_zero : (thirdClass : (ℚ × ℚ) ⧸ integerLattice) ≠ 0 := by
  intro h
  have hmem := (eq_zero_iff ((0, 1 / 3) : ℚ × ℚ)).mp h
  exact third_not_integer (AddSubgroup.mem_prod.mp hmem).2

private theorem firstImageClass_ne_zero : firstImageClass ≠ 0 := by
  intro h
  have hmem : (firstBasis : ℚ × ℚ) ∈ integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ)) :=
    (eq_zero_iff firstBasis).mp h
  have hpre : diagonal.symm (firstBasis : ℚ × ℚ) ∈ integerLattice :=
    AddSubgroup.mem_map_equiv.mp hmem
  rw [diagonal_symm_first] at hpre
  exact half_not_integer (AddSubgroup.mem_prod.mp hpre).1

private theorem secondImageClass_ne_zero : secondImageClass ≠ 0 := by
  intro h
  have hmem : (secondBasis : ℚ × ℚ) ∈ integerLattice.map (diagonal : (ℚ × ℚ) →+ (ℚ × ℚ)) :=
    (eq_zero_iff secondBasis).mp h
  have hpre : diagonal.symm (secondBasis : ℚ × ℚ) ∈ integerLattice :=
    AddSubgroup.mem_map_equiv.mp hmem
  rw [diagonal_symm_second] at hpre
  exact third_not_integer (AddSubgroup.mem_prod.mp hpre).2

/-- Both coordinate classes are nonzero independently on each side of the comparison. -/
private theorem diagonal_classes_nonzero :
    halfClass ≠ 0 ∧ thirdClass ≠ 0 ∧ firstImageClass ≠ 0 ∧ secondImageClass ≠ 0 := by
  refine ⟨?_, ?_, firstImageClass_ne_zero, secondImageClass_ne_zero⟩
  · intro h
    exact halfClass_ne_zero (congrArg Subtype.val h)
  · intro h
    exact thirdClass_ne_zero (congrArg Subtype.val h)

/-- The quotient-kernel comparison and its inverse have the two expected coordinate values. -/
private theorem diagonal_quotient_values :
    let E := kerMapEquivQuotientOfEquiv integerLattice integerLattice diagonal diagonal_preserves
    E halfClass = firstImageClass ∧ E thirdClass = secondImageClass ∧
      ((E.symm firstImageClass : diagonalQuotient.ker) : (ℚ × ℚ) ⧸ integerLattice) =
        (halfClass : (ℚ × ℚ) ⧸ integerLattice) ∧
      ((E.symm secondImageClass : diagonalQuotient.ker) : (ℚ × ℚ) ⧸ integerLattice) =
        (thirdClass : (ℚ × ℚ) ⧸ integerLattice) := by
  dsimp only
  have hh : diagonal ((1 / 2, 0) : ℚ × ℚ) ∈ integerLattice := by
    rw [diagonal_half_first]
    exact firstBasis.property
  have ht : diagonal ((0, 1 / 3) : ℚ × ℚ) ∈ integerLattice := by
    rw [diagonal_third_second]
    exact secondBasis.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := kerMapEquivQuotientOfEquiv_apply_mk integerLattice integerLattice
      diagonal diagonal_preserves ((1 / 2, 0) : ℚ × ℚ) hh
    have hb : (⟨diagonal ((1 / 2, 0) : ℚ × ℚ), hh⟩ : integerLattice) = firstBasis :=
      Subtype.ext diagonal_half_first
    rw [hb] at h
    exact h
  · have h := kerMapEquivQuotientOfEquiv_apply_mk integerLattice integerLattice
      diagonal diagonal_preserves ((0, 1 / 3) : ℚ × ℚ) ht
    have hb : (⟨diagonal ((0, 1 / 3) : ℚ × ℚ), ht⟩ : integerLattice) = secondBasis :=
      Subtype.ext diagonal_third_second
    rw [hb] at h
    exact h
  · have h := kerMapEquivQuotientOfEquiv_symm_apply_mk integerLattice integerLattice
      diagonal diagonal_preserves firstBasis
    simpa only [diagonal_symm_first, firstImageClass, halfClass] using h
  · have h := kerMapEquivQuotientOfEquiv_symm_apply_mk integerLattice integerLattice
      diagonal diagonal_preserves secondBasis
    simpa only [diagonal_symm_second, secondImageClass, thirdClass] using h

end QuotientAddGroup
