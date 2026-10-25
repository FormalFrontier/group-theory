/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.Units
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.ZMod

/-!
# Rational and integer examples for density on units

The rational inclusion satisfies the density, unit-reflection, and open-unit-coercion
hypotheses independently of `DenseRange.units_map`. The integer quotient modulo five has
dense range and an open unit coercion, but its unit image misses the unit of value two.
The final rational unit-density example invokes `DenseRange.units_map`.
-/

private theorem rational_cast_dense_local_open :
    DenseRange ((Rat.castHom ℝ).toMonoidHom) ∧
      IsLocalHom ((Rat.castHom ℝ).toMonoidHom) ∧
      Topology.IsOpenEmbedding (Units.val : ℝˣ → ℝ) := by
  refine ⟨Rat.denseRange_cast (𝕜 := ℝ), ?_,
    IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)⟩
  exact isLocalHom_of_exists_map_ne_one
    (f := (Rat.castHom ℝ).toMonoidHom) ⟨0, by simp⟩

private theorem integer_cast_zmod_five_unit_obstruction :
    Function.Surjective ((Int.castRingHom (ZMod 5)).toMonoidHom) ∧
      Topology.IsOpenEmbedding (Units.val : (ZMod 5)ˣ → ZMod 5) ∧
      ZMod.unitOfCoprime (n := 5) 2 (by decide) ∉
        Set.range (Units.map ((Int.castRingHom (ZMod 5)).toMonoidHom)) ∧
      ¬ DenseRange (Units.map ((Int.castRingHom (ZMod 5)).toMonoidHom)) ∧
      ¬ IsLocalHom ((Int.castRingHom (ZMod 5)).toMonoidHom) := by
  have hmiss : ZMod.unitOfCoprime (n := 5) 2 (by decide) ∉
      Set.range (Units.map ((Int.castRingHom (ZMod 5)).toMonoidHom)) := by
    rintro ⟨u, hu⟩
    have hval : ((u : ℤ) : ZMod 5) = 2 := by
      simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        Int.coe_castRingHom, ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using
        congrArg (fun v : (ZMod 5)ˣ => (v : ZMod 5)) hu
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact (by decide : (1 : ZMod 5) ≠ 2) (by simpa using hval)
    · exact (by decide : (-1 : ZMod 5) ≠ 2) (by simpa using hval)
  refine ⟨ZMod.intCast_surjective (n := 5),
    IsOpenUnits.isOpenEmbedding_unitsVal (M := ZMod 5), hmiss, ?_, ?_⟩
  · intro h
    exact hmiss ((denseRange_discrete.mp h)
      (ZMod.unitOfCoprime (n := 5) 2 (by decide)))
  · rintro ⟨hreflect⟩
    have htwo : IsUnit (((Int.castRingHom (ZMod 5)).toMonoidHom) (2 : ℤ)) := by
      refine ⟨ZMod.unitOfCoprime (n := 5) 2 (by decide), ?_⟩
      simp only [ZMod.coe_unitOfCoprime, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, Int.coe_castRingHom, Int.cast_ofNat, Nat.cast_ofNat]
    have hnonunit : ¬ IsUnit (2 : ℤ) := by simp [Int.isUnit_iff]
    exact hnonunit (hreflect (2 : ℤ) htwo)

private theorem rational_cast_units_dense :
    DenseRange (Units.map ((Rat.castHom ℝ).toMonoidHom)) := by
  obtain ⟨hdense, hlocal, hopen⟩ := rational_cast_dense_local_open
  let : IsLocalHom ((Rat.castHom ℝ).toMonoidHom) := hlocal
  exact hdense.units_map hopen
