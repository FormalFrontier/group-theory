/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.QuotientTorsion
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# A nonzero torsion class in the rational quotient by the integers

For `L = AddSubgroup.zmultiples (1 : ℚ)`, the class of `1 / 2` is nonzero
and killed by `2`. The quotient-torsion equivalence sends it to the class
of the integer `1` modulo `2L`, with the stated inverse. The hypotheses,
nonzero class and characteristic value are asserted together, rather than
assuming ambient bijectivity or assuming the torsion witness.
-/

/-- In `ℚ / ℤ`, the nonzero class of `1 / 2` corresponds to `1` modulo `2ℤ`. -/
private theorem rational_half_torsion :
    let L := AddSubgroup.zmultiples (1 : ℚ)
    ∃ (hn : Function.Bijective (nsmulAddMonoidHom (α := ℚ) 2))
      (hx : ((1 / 2 : ℚ) : ℚ ⧸ L) ∈
        (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker),
      ((1 / 2 : ℚ) : ℚ ⧸ L) ≠ 0 ∧
      QuotientAddGroup.nsmulTorsionEquivQuotient L 2 hn
          ⟨((1 / 2 : ℚ) : ℚ ⧸ L), hx⟩ =
        ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
          L ⧸ (nsmulAddMonoidHom (α := L) 2).range) ∧
      ((QuotientAddGroup.nsmulTorsionEquivQuotient L 2 hn).symm
        ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
          L ⧸ (nsmulAddMonoidHom (α := L) 2).range) : ℚ ⧸ L) =
        ((1 / 2 : ℚ) : ℚ ⧸ L) := by
  let L := AddSubgroup.zmultiples (1 : ℚ)
  have hn : Function.Bijective (nsmulAddMonoidHom (α := ℚ) 2) := by
    constructor
    · intro a b hab
      exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0)
        (by simpa only [nsmulAddMonoidHom_apply, nsmul_eq_mul, Nat.cast_ofNat] using hab)
    · intro q
      refine ⟨q / 2, ?_⟩
      simpa only [nsmulAddMonoidHom_apply, nsmul_eq_mul, Nat.cast_ofNat] using
        (mul_div_cancel₀ q (by norm_num : (2 : ℚ) ≠ 0))
  have hhalf : 2 • (1 / 2 : ℚ) = 1 := by norm_num [nsmul_eq_mul]
  have hmem : 2 • (1 / 2 : ℚ) ∈ L := by
    rw [hhalf]
    exact AddSubgroup.mem_zmultiples (1 : ℚ)
  have hx : ((1 / 2 : ℚ) : ℚ ⧸ L) ∈
      (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker := by
    change 2 • ((1 / 2 : ℚ) : ℚ ⧸ L) = 0
    rw [← QuotientAddGroup.mk_nsmul]
    exact (QuotientAddGroup.eq_zero_iff (2 • (1 / 2 : ℚ))).mpr hmem
  refine ⟨hn, hx, ?_, ?_⟩
  · intro hzero
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp
      ((QuotientAddGroup.eq_zero_iff (1 / 2 : ℚ)).mp hzero)
    have hz' : (z : ℚ) = 1 / 2 := by simpa only [zsmul_eq_mul, mul_one] using hz
    have hden := congrArg Rat.den hz'
    rw [Rat.div_def', Rat.den_divInt] at hden
    norm_num at hden
  · have hforward :=
      QuotientAddGroup.nsmulTorsionEquivQuotient_apply_mk L 2 hn (1 / 2 : ℚ) hmem
    have hvalue : (⟨2 • (1 / 2 : ℚ), hmem⟩ : L) =
        ⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ := Subtype.ext hhalf
    rw [hvalue] at hforward
    refine ⟨hforward, ?_⟩
    rw [← hforward]
    exact congrArg Subtype.val
      ((QuotientAddGroup.nsmulTorsionEquivQuotient L 2 hn).symm_apply_apply _)

/-- At `n = 1`, both sides of the quotient-torsion equivalence are trivial. -/
private theorem one_torsion_boundary {V : Type*} [AddCommGroup V] (L : AddSubgroup V) :
    Function.Bijective (nsmulAddMonoidHom (α := V) 1) ∧
      Subsingleton (nsmulAddMonoidHom (α := V ⧸ L) 1).ker ∧
      Subsingleton (L ⧸ (nsmulAddMonoidHom (α := L) 1).range) := by
  have hV : nsmulAddMonoidHom (α := V) 1 = AddMonoidHom.id V := by
    apply AddMonoidHom.ext
    intro a
    exact one_nsmul a
  have hQ : nsmulAddMonoidHom (α := V ⧸ L) 1 = AddMonoidHom.id (V ⧸ L) := by
    apply AddMonoidHom.ext
    intro a
    exact one_nsmul a
  have hL : nsmulAddMonoidHom (α := L) 1 = AddMonoidHom.id L := by
    apply AddMonoidHom.ext
    intro a
    exact one_nsmul a
  refine ⟨?_, ?_, ?_⟩
  · rw [hV]
    exact Function.bijective_id
  · rw [hQ, AddMonoidHom.ker_id]
    infer_instance
  · have hrange : (AddMonoidHom.id L).range = ⊤ :=
      AddMonoidHom.range_eq_top.mpr Function.surjective_id
    rw [hL, hrange]
    exact QuotientAddGroup.subsingleton_quotient_top
