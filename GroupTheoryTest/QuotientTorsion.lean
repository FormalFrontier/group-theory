/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.QuotientTorsion.Cardinality
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Scalar torsion classes in the rational quotient by the integers

For `L = AddSubgroup.zmultiples (1 : ℚ)`, the class of `1 / 2` is nonzero
and killed by `2`. The quotient-torsion equivalence sends it to the class
of the integer `1` modulo `2L`, with the stated inverse. The hypotheses,
nonzero class and characteristic value are asserted together, rather than
assuming ambient bijectivity or assuming the torsion witness.

The nonzero quarter-class maps by doubling to the nonzero half-class.
The corresponding equivalence values are both computed as `[1]` using the
representative API. The scalar-transition identity then identifies the
reduction of the first value with the second. Including that same half-class
back into the four-torsion gives `[2]` modulo `4L`, as does doubling its value
modulo `2L`. Nonvanishing of `[2]` modulo `4L` is proved from quotient membership
and the nonintegrality of `1 / 2`, independently of either equivalence.

The same rational model has a finitely generated rank-one integer subgroup
and exactly two doubling-torsion classes. This count uses the original
quotient-torsion equivalence and Mathlib's free scalar-index formula, independently
of the general finite-kernel and cardinality theorems. Both general theorems
are also instantiated on this rational model. The zero scalar on a trivial
ambient group and doubling on `ZMod 3` supply boundary cases.
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

/-- Doubling takes the nonzero quarter-class in `ℚ / ℤ` to the nonzero half-class.
Both equivalences send these classes to `[1]`, and reduction carries the first
value to the second. Including the same half-class into the four-torsion and
doubling its lattice value both give `[2]` modulo `4ℤ`. That target class is
nonzero by a quotient-membership argument independent of the equivalences. -/
private theorem rational_quarter_to_half :
    let L := AddSubgroup.zmultiples (1 : ℚ)
    let reduction : (L ⧸ (nsmulAddMonoidHom (α := L) 4).range) →+
        L ⧸ (nsmulAddMonoidHom (α := L) 2).range :=
      QuotientAddGroup.map _ _ (AddMonoidHom.id L) (by
        simpa only [AddSubgroup.comap_id] using
          AddMonoidHom.range_nsmul_mul_le (A := L) 2 2)
    let torsionMap : (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker →+
        (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker :=
      AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker 2 2)
    let inclusion : (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker →+
        (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker :=
      AddSubgroup.inclusion (by
        intro q hq
        change 2 • q = 0 at hq
        change (2 * 2) • q = 0
        rw [mul_nsmul', hq, nsmul_zero])
    let quotientDouble : (L ⧸ (nsmulAddMonoidHom (α := L) 2).range) →+
        L ⧸ (nsmulAddMonoidHom (α := L) 4).range :=
      QuotientAddGroup.map _ _ (nsmulAddMonoidHom (α := L) 2) (by
        rintro _ ⟨l, rfl⟩
        exact ⟨l, mul_nsmul' l 2 2⟩)
    let two : L := ⟨2, AddSubgroup.mem_zmultiples_iff.mpr ⟨2, by norm_num⟩⟩
    ∃ (h4 : Function.Bijective (nsmulAddMonoidHom (α := ℚ) 4))
      (x : (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker),
      (x : ℚ ⧸ L) = ((1 / 4 : ℚ) : ℚ ⧸ L) ∧
      (x : ℚ ⧸ L) ≠ 0 ∧
      (torsionMap x : ℚ ⧸ L) = ((1 / 2 : ℚ) : ℚ ⧸ L) ∧
      (torsionMap x : ℚ ⧸ L) ≠ 0 ∧
      QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 x =
        ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
          L ⧸ (nsmulAddMonoidHom (α := L) 4).range) ∧
      QuotientAddGroup.nsmulTorsionEquivQuotient L 2
          (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4) (torsionMap x) =
        ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
          L ⧸ (nsmulAddMonoidHom (α := L) 2).range) ∧
      reduction (QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 x) =
        QuotientAddGroup.nsmulTorsionEquivQuotient L 2
          (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4) (torsionMap x) ∧
      (inclusion (torsionMap x) : ℚ ⧸ L) = ((1 / 2 : ℚ) : ℚ ⧸ L) ∧
      (inclusion (torsionMap x) : ℚ ⧸ L) ≠ 0 ∧
      QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 (inclusion (torsionMap x)) =
        (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) ∧
      quotientDouble (QuotientAddGroup.nsmulTorsionEquivQuotient L 2
          (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4) (torsionMap x)) =
        (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) ∧
      QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 (inclusion (torsionMap x)) =
        quotientDouble (QuotientAddGroup.nsmulTorsionEquivQuotient L 2
          (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4) (torsionMap x)) ∧
      (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) ≠ 0 := by
  let L := AddSubgroup.zmultiples (1 : ℚ)
  let inclusion : (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker →+
      (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker :=
    AddSubgroup.inclusion (by
      intro q hq
      change 2 • q = 0 at hq
      change (2 * 2) • q = 0
      rw [mul_nsmul', hq, nsmul_zero])
  let quotientDouble : (L ⧸ (nsmulAddMonoidHom (α := L) 2).range) →+
      L ⧸ (nsmulAddMonoidHom (α := L) 4).range :=
    QuotientAddGroup.map _ _ (nsmulAddMonoidHom (α := L) 2) (by
      rintro _ ⟨l, rfl⟩
      exact ⟨l, mul_nsmul' l 2 2⟩)
  let two : L := ⟨2, AddSubgroup.mem_zmultiples_iff.mpr ⟨2, by norm_num⟩⟩
  obtain ⟨h2, hhalf, hhalf_ne, hhalf_image, _⟩ := rational_half_torsion
  -- A putative fourth multiple equal to two would make the half integral.
  have hfour_half : 4 • (1 / 2 : ℚ) = 2 := by norm_num [nsmul_eq_mul]
  have htwo_ne : (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) ≠ 0 := by
    intro hzero
    obtain ⟨l, hl⟩ := (QuotientAddGroup.eq_zero_iff two).mp hzero
    have hl' : 4 • (l : ℚ) = 2 := congrArg Subtype.val hl
    have hlhalf : (l : ℚ) = 1 / 2 := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℚ) ≠ 0)
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hl'.trans hfour_half.symm
    apply hhalf_ne
    exact (QuotientAddGroup.eq_zero_iff (1 / 2 : ℚ)).mpr (hlhalf ▸ l.property)
  have h4 : Function.Bijective (nsmulAddMonoidHom (α := ℚ) 4) := by
    have hcomp : nsmulAddMonoidHom (α := ℚ) 4 =
        (nsmulAddMonoidHom 2).comp (nsmulAddMonoidHom 2) := by
      ext q
      norm_num [nsmul_eq_mul, ← mul_assoc]
    rw [hcomp]
    exact h2.comp h2
  have hquarter : 4 • (1 / 4 : ℚ) = 1 := by norm_num [nsmul_eq_mul]
  have hmem : 4 • (1 / 4 : ℚ) ∈ L := by
    rw [hquarter]
    exact AddSubgroup.mem_zmultiples (1 : ℚ)
  have hx : ((1 / 4 : ℚ) : ℚ ⧸ L) ∈
      (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker := by
    change 4 • ((1 / 4 : ℚ) : ℚ ⧸ L) = 0
    rw [← QuotientAddGroup.mk_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hmem
  let x : (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker := ⟨_, hx⟩
  have hdouble : 2 • (x : ℚ ⧸ L) = ((1 / 2 : ℚ) : ℚ ⧸ L) := by
    change 2 • ((1 / 4 : ℚ) : ℚ ⧸ L) = _
    rw [← QuotientAddGroup.mk_nsmul]
    norm_num [nsmul_eq_mul]
  have himage4 : QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 x =
      ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
        L ⧸ (nsmulAddMonoidHom (α := L) 4).range) := by
    have hforward :=
      QuotientAddGroup.nsmulTorsionEquivQuotient_apply_mk L 4 h4 (1 / 4 : ℚ) hmem
    have hvalue : (⟨4 • (1 / 4 : ℚ), hmem⟩ : L) =
        ⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ := Subtype.ext hquarter
    rw [hvalue] at hforward
    exact hforward
  have himage2 : QuotientAddGroup.nsmulTorsionEquivQuotient L 2
      (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4)
      (AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker 2 2) x) =
      ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
        L ⧸ (nsmulAddMonoidHom (α := L) 2).range) := by
    have hvalue : AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker 2 2) x =
        (⟨((1 / 2 : ℚ) : ℚ ⧸ L), hhalf⟩ :
          (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker) := Subtype.ext hdouble
    rw [hvalue]
    exact hhalf_image
  let y := AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker 2 2) x
  have hinclusion_half : (inclusion y : ℚ ⧸ L) = ((1 / 2 : ℚ) : ℚ ⧸ L) :=
    (AddSubgroup.coe_inclusion _ y).trans hdouble
  have hinclusion_ne : (inclusion y : ℚ ⧸ L) ≠ 0 := by
    simpa only [hinclusion_half] using hhalf_ne
  have hhalfmem4 : 4 • (1 / 2 : ℚ) ∈ L := by
    rw [hfour_half]
    exact two.property
  have hinclusion_value : QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4
      (inclusion y) = (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) := by
    have hvalue : inclusion y =
        (⟨((1 / 2 : ℚ) : ℚ ⧸ L), by
          change 4 • ((1 / 2 : ℚ) : ℚ ⧸ L) = 0
          rw [← QuotientAddGroup.mk_nsmul]
          exact (QuotientAddGroup.eq_zero_iff (4 • (1 / 2 : ℚ))).mpr hhalfmem4⟩ :
          (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker) := Subtype.ext hinclusion_half
    rw [hvalue]
    have hforward :=
      QuotientAddGroup.nsmulTorsionEquivQuotient_apply_mk L 4 h4 (1 / 2 : ℚ) hhalfmem4
    have htwo_value : (⟨4 • (1 / 2 : ℚ), hhalfmem4⟩ : L) = two :=
      Subtype.ext hfour_half
    rw [htwo_value] at hforward
    exact hforward
  have hquotient_value : quotientDouble (QuotientAddGroup.nsmulTorsionEquivQuotient L 2
      (AddMonoidHom.nsmul_bijective_of_mul 2 2 h4) y) =
      (two : L ⧸ (nsmulAddMonoidHom (α := L) 4).range) := by
    rw [himage2]
    simp only [quotientDouble, QuotientAddGroup.map_mk]
    apply congrArg (fun l : L => (l : L ⧸ (nsmulAddMonoidHom (α := L) 4).range))
    apply Subtype.ext
    change 2 • (1 : ℚ) = 2
    norm_num [nsmul_eq_mul]
  -- Use the ambient square with f₂ = μ₂, f₄ = μ₄, a = id and b = μ₂.
  let h2' := AddMonoidHom.nsmul_bijective_of_mul 2 2 h4
  let f2 := AddEquiv.ofBijective (nsmulAddMonoidHom (α := ℚ) 2) h2'
  let f4 := AddEquiv.ofBijective (nsmulAddMonoidHom (α := ℚ) 4) h4
  let hf2 : L.map (f2 : ℚ →+ ℚ) ≤ L :=
    AddSubgroup.map_le_iff_le_comap.mpr (by intro q hq; exact L.nsmul_mem hq 2)
  let hf4 : L.map (f4 : ℚ →+ ℚ) ≤ L :=
    AddSubgroup.map_le_iff_le_comap.mpr (by intro q hq; exact L.nsmul_mem hq 4)
  let c2 := AddEquiv.addSubgroupCongr
    (congrArg AddMonoidHom.ker (QuotientAddGroup.map_nsmulAddMonoidHom L 2).symm)
  let c4 := AddEquiv.addSubgroupCongr
    (congrArg AddMonoidHom.ker (QuotientAddGroup.map_nsmulAddMonoidHom L 4).symm)
  let e2 := QuotientAddGroup.quotientAddEquivOfEq
    (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L 2)
  let e4 := QuotientAddGroup.quotientAddEquivOfEq
    (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L 4)
  have hquotient_id (q : ℚ ⧸ L) :
      QuotientAddGroup.map L L (AddMonoidHom.id ℚ)
        (by intro q hq; exact hq) q = q :=
    QuotientAddGroup.map_id_apply L (by intro q hq; exact hq) q
  let kernelMap :
      (QuotientAddGroup.map L L (f2 : ℚ →+ ℚ)
        (AddSubgroup.map_le_iff_le_comap.mp hf2)).ker →+
      (QuotientAddGroup.map L L (f4 : ℚ →+ ℚ)
        (AddSubgroup.map_le_iff_le_comap.mp hf4)).ker :=
    AddMonoidHom.restrict (f := QuotientAddGroup.map L L (AddMonoidHom.id ℚ)
      (by intro q hq; exact hq)) (by
        have hf2' : (f2 : ℚ →+ ℚ) = nsmulAddMonoidHom (α := ℚ) 2 := rfl
        have hf4' : (f4 : ℚ →+ ℚ) = nsmulAddMonoidHom (α := ℚ) 4 := rfl
        intro q hq
        have hq2 : q ∈ (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker := by
          simpa only [hf2', QuotientAddGroup.map_nsmulAddMonoidHom,
            SetLike.mem_coe, AddSubgroup.mem_toAddSubmonoid] using hq
        have hq4 : q ∈ (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker :=
          (inclusion ⟨q, hq2⟩).property
        have hq4' : QuotientAddGroup.map L L (AddMonoidHom.id ℚ)
            (by intro q hq; exact hq) q ∈
              (nsmulAddMonoidHom (α := ℚ ⧸ L) 4).ker :=
          (hquotient_id q).symm ▸ hq4
        simpa only [hf4', QuotientAddGroup.map_nsmulAddMonoidHom,
          SetLike.mem_coe, AddSubgroup.mem_toAddSubmonoid] using hq4')
  have hcomm : ∀ q : ℚ, f4 ((AddMonoidHom.id ℚ) q) = nsmulAddMonoidHom 2 (f2 q) :=
    fun q => mul_nsmul' q 2 2
  let subgroupMap : L →+ L :=
    AddMonoidHom.restrict (f := nsmulAddMonoidHom (α := ℚ) 2)
      (by intro q hq; exact L.nsmul_mem hq 2)
  let latticeMap := QuotientAddGroup.map ((L.map (f2 : ℚ →+ ℚ)).addSubgroupOf L)
      ((L.map (f4 : ℚ →+ ℚ)).addSubgroupOf L) subgroupMap (by
        intro l hl
        change (l : ℚ) ∈ L.map (f2 : ℚ →+ ℚ) at hl
        change nsmulAddMonoidHom 2 (l : ℚ) ∈ L.map (f4 : ℚ →+ ℚ)
        obtain ⟨q, hq, hql⟩ := AddSubgroup.mem_map.mp hl
        exact AddSubgroup.mem_map.mpr
          ⟨q, hq, (hcomm q).trans (congrArg (nsmulAddMonoidHom 2) hql)⟩)
  have square : latticeMap.comp
        (QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f2 hf2).toAddMonoidHom =
      (QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f4 hf4).toAddMonoidHom.comp
        kernelMap :=
    QuotientAddGroup.kerMapEquivQuotientOfEquiv_naturality L L f2 hf2 L L f4 hf4
      (AddMonoidHom.id ℚ) (nsmulAddMonoidHom 2)
      (by intro q hq; exact hq) (by intro q hq; exact L.nsmul_mem hq 2) hcomm
  have hquot (z : L ⧸ (L.map (f2 : ℚ →+ ℚ)).addSubgroupOf L) :
      quotientDouble (e2 z) = e4 (latticeMap z) := by
    obtain ⟨l, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    simp only [quotientDouble, e2, e4, latticeMap]; rfl
  have hkernel : kernelMap (c2 y) = c4 (inclusion y) := by
    apply Subtype.ext
    change QuotientAddGroup.map L L (AddMonoidHom.id ℚ)
      (by intro q hq; exact hq) (c2 y : ℚ ⧸ L) =
        (c4 (inclusion y) : ℚ ⧸ L)
    exact (hquotient_id (c2 y : ℚ ⧸ L)).trans (by
      simpa only [c2, c4, AddEquiv.addSubgroupCongr_apply] using
        (AddSubgroup.coe_inclusion _ y).symm)
  have hpoint : latticeMap
        (QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f2 hf2 (c2 y)) =
      QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f4 hf4 (kernelMap (c2 y)) :=
    DFunLike.congr_fun square (c2 y)
  have hcommute : QuotientAddGroup.nsmulTorsionEquivQuotient L 4 h4 (inclusion y) =
      quotientDouble (QuotientAddGroup.nsmulTorsionEquivQuotient L 2 h2' y) := by
    rw [QuotientAddGroup.nsmulTorsionEquivQuotient_eq_kerMapEquivQuotientOfEquiv,
      QuotientAddGroup.nsmulTorsionEquivQuotient_eq_kerMapEquivQuotientOfEquiv]
    change e4 (QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f4 hf4 (c4 (inclusion y))) =
      quotientDouble (e2 (QuotientAddGroup.kerMapEquivQuotientOfEquiv L L f2 hf2 (c2 y)))
    rw [hquot, hpoint, hkernel]
  refine ⟨h4, x, rfl, ?_, hdouble, ?_, himage4, himage2, ?_, hinclusion_half,
    hinclusion_ne, hinclusion_value, hquotient_value,
    hcommute, htwo_ne⟩
  · intro hzero
    apply hhalf_ne
    rw [← hdouble, hzero, nsmul_zero]
  · change 2 • (x : ℚ ⧸ L) ≠ 0
    simpa only [hdouble] using hhalf_ne
  · exact DFunLike.congr_fun
      (QuotientAddGroup.nsmulTorsionEquivQuotient_naturality L 2 2 h4) x

/-- With transition multiplier `1`, the stock kernel restriction preserves each element. -/
private theorem one_transition_boundary {A : Type*} [AddCommGroup A] (m : ℕ)
    (x : (nsmulAddMonoidHom (α := A) (m * 1)).ker) :
    (AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker m 1) x : A) = (x : A) :=
  one_nsmul _

/-- The integer subgroup in the rational half-class model is finitely generated of rank one,
and Mathlib's finite-free index formula gives exactly two doubling-torsion classes. -/
private theorem rational_doubling_cardinality :
    let L := AddSubgroup.zmultiples (1 : ℚ)
    AddGroup.FG L ∧ Module.finrank ℤ L = 1 ∧
      ∃ (hn : Function.Bijective (nsmulAddMonoidHom (α := ℚ) 2))
        (hx : ((1 / 2 : ℚ) : ℚ ⧸ L) ∈
          (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker),
        Finite (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker ∧
        Nat.card (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker = 2 ∧
        ((1 / 2 : ℚ) : ℚ ⧸ L) ≠ 0 ∧
        QuotientAddGroup.nsmulTorsionEquivQuotient L 2 hn
            ⟨((1 / 2 : ℚ) : ℚ ⧸ L), hx⟩ =
          ((⟨1, AddSubgroup.mem_zmultiples (1 : ℚ)⟩ : L) :
            L ⧸ (nsmulAddMonoidHom (α := L) 2).range) := by
  let L := AddSubgroup.zmultiples (1 : ℚ)
  let f : ℤ →+ L :=
    { toFun := fun z => ⟨z • (1 : ℚ), AddSubgroup.zsmul_mem_zmultiples 1 z⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      have h' := congrArg Subtype.val h
      simpa [f, zsmul_eq_mul] using h'
    · rintro ⟨q, hq⟩
      obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
      exact ⟨z, Subtype.ext hz⟩
  let e : ℤ ≃ₗ[ℤ] L := (AddEquiv.ofBijective f hf).toIntLinearEquiv
  let : Module.Free ℤ L := Module.Free.of_equiv e
  let : Module.Finite ℤ L := Module.Finite.equiv e
  have hFG : AddGroup.FG L := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hrank : Module.finrank ℤ L = 1 :=
    e.finrank_eq.symm.trans (Module.finrank_self ℤ)
  obtain ⟨hn, hx, hnonzero, hforward, _hinverse⟩ := rational_half_torsion
  have hcard : Nat.card (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker = 2 := by
    calc
      _ = Nat.card (L ⧸ (nsmulAddMonoidHom (α := L) 2).range) :=
        Nat.card_congr (QuotientAddGroup.nsmulTorsionEquivQuotient L 2 hn).toEquiv
      _ = (nsmulAddMonoidHom (α := L) 2).range.index :=
        (AddSubgroup.index_eq_card _).symm
      _ = 2 ^ Module.finrank ℤ L := AddSubgroup.index_range_nsmul L 2
      _ = 2 := by rw [hrank]; norm_num
  exact ⟨hFG, hrank, hn, hx, Nat.finite_of_card_ne_zero (by rw [hcard]; decide),
    hcard, hnonzero, hforward⟩

/-- Doubling on the rational quotient by the integers has finite kernel of cardinality two. -/
private theorem rational_doubling_quotient_torsion :
    let L := AddSubgroup.zmultiples (1 : ℚ)
    Finite (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker ∧
      Nat.card (nsmulAddMonoidHom (α := ℚ ⧸ L) 2).ker = 2 := by
  let L := AddSubgroup.zmultiples (1 : ℚ)
  obtain ⟨hFG, hrank, hn, _hx, _hfinite, _hcard, _hnonzero, _hforward⟩ :=
    rational_doubling_cardinality
  let : AddGroup.FG L := hFG
  refine ⟨QuotientAddGroup.finite_ker_nsmul_quotient L 2 hn, ?_⟩
  exact (QuotientAddGroup.natCard_ker_nsmul_quotient L 2 hn).trans (by rw [hrank]; norm_num)

/-- Zero is a permitted scalar when the ambient group is trivial; the count is `0^0 = 1`. -/
private theorem zero_torsion_cardinality :
    let L : AddSubgroup PUnit := ⊤
    AddGroup.FG L ∧ Function.Bijective (nsmulAddMonoidHom (α := PUnit) 0) ∧
      Module.finrank ℤ L = 0 ∧
      Finite (nsmulAddMonoidHom (α := PUnit ⧸ L) 0).ker ∧
      Nat.card (nsmulAddMonoidHom (α := PUnit ⧸ L) 0).ker =
        0 ^ Module.finrank ℤ L := by
  let L : AddSubgroup PUnit := ⊤
  let : Subsingleton (PUnit ⧸ L) := QuotientAddGroup.subsingleton_quotient_top
  refine ⟨inferInstance, ?_, Module.finrank_zero_of_subsingleton, inferInstance, ?_⟩
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨x, Subsingleton.elim _ _⟩⟩
  · rw [Module.finrank_zero_of_subsingleton, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Nonzero finite torsion in `L` is allowed: doubling on `ZMod 3` is bijective,
while the whole subgroup has integer rank zero and the quotient kernel has one element. -/
private theorem finite_torsion_subgroup_cardinality :
    let L : AddSubgroup (ZMod 3) := ⊤
    AddGroup.FG L ∧ Function.Bijective (nsmulAddMonoidHom (α := ZMod 3) 2) ∧
      Module.finrank ℤ L = 0 ∧
      (∃ x : L, x ≠ 0 ∧ (3 : ℕ) • x = 0) ∧
      Finite (nsmulAddMonoidHom (α := ZMod 3 ⧸ L) 2).ker ∧
      Nat.card (nsmulAddMonoidHom (α := ZMod 3 ⧸ L) 2).ker =
        2 ^ Module.finrank ℤ L := by
  let L : AddSubgroup (ZMod 3) := ⊤
  let : Subsingleton (ZMod 3 ⧸ L) := QuotientAddGroup.subsingleton_quotient_top
  have hrank : Module.finrank ℤ L = 0 :=
    (isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite).finrank_eq_zero
  refine ⟨inferInstance, ?_, hrank, ?_, inferInstance, ?_⟩
  · have hcoprime : Nat.Coprime (Nat.card (ZMod 3)) 2 := by
      norm_num [Nat.card_eq_fintype_card, ZMod.card]
      decide
    exact Nat.Coprime.nsmul_right_bijective hcoprime
  · refine ⟨⟨1, AddSubgroup.mem_top _⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      exact (by decide : (1 : ZMod 3) ≠ 0) h'
    · apply Subtype.ext
      exact ZModModule.char_nsmul_eq_zero 3 1
  · rw [hrank, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
