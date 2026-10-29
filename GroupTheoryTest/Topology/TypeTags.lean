/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.TypeTags
import GroupTheory.Topology.RationalCircle
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# One-sided type-tag transport

The weak homeomorphism applies to a noncommutative discrete transformation monoid.
The additive equivalence transports an order-three circle character on the original
additive integers, including its nonzero value at one and its vanishing at three.
The rational-circle comparison is compatible with precomposition in independent universes.
-/

open scoped Topology

universe u v

private abbrev Transform := Function.End (Fin 2)

private instance : TopologicalSpace Transform := ⊥

private instance : DiscreteTopology Transform := ⟨rfl⟩

example :
    let c₀ : Transform := fun _ => 0
    let c₁ : Transform := fun _ => 1
    c₀ * c₁ ≠ c₁ * c₀ ∧
      ContinuousMonoidHom.toAdditiveRight.symm
        (ContinuousAddMonoidHom.id (Additive Transform))
        (Multiplicative.ofAdd (Additive.ofMul c₀)) = c₀ := by
  constructor
  · intro h
    have := congrFun h 0
    exact Fin.zero_ne_one this
  · rw [ContinuousMonoidHom.toAdditiveRight_symm_apply]
    rfl

private noncomputable def cubicMonoidCharacter : PontryaginDual (Multiplicative ℤ) where
  toFun n := Circle.exp (2 * Real.pi / 3 * (n.toAdd : ℝ))
  map_one' := by simp
  map_mul' m n := by
    change Circle.exp (2 * Real.pi / 3 * ((m.toAdd + n.toAdd : ℤ) : ℝ)) = _
    rw [Int.cast_add, mul_add, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

private noncomputable def cubicCharacter : ℤ →ₜ+ Additive Circle :=
  ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv
    (Additive.ofMul cubicMonoidCharacter)

example : cubicCharacter 3 = 0 ∧ cubicCharacter 1 ≠ 0 := by
  have value (n : ℤ) : cubicCharacter n =
      Additive.ofMul (Circle.exp (2 * Real.pi / 3 * (n : ℝ))) := by
    rw [cubicCharacter, ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv_apply,
      ContinuousMonoidHom.toAdditiveRight_apply]
    rfl
  constructor
  · rw [value]
    have h : (2 * Real.pi / 3 * (3 : ℝ)) = 2 * Real.pi := by ring
    simp only [Int.cast_ofNat, h, Circle.exp_two_pi]
    rfl
  · rw [value]
    intro h
    have he : Circle.exp (2 * Real.pi / 3) = 1 := by
      simpa using congrArg Additive.toMul h
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp he
    have hn' : (n : ℝ) = 1 / 3 := by nlinarith [Real.pi_pos]
    have hn₀ : (0 : ℤ) < n := by
      exact_mod_cast (show (0 : ℝ) < n by rw [hn']; norm_num)
    have hn₁ : n < (1 : ℤ) := by
      exact_mod_cast (show (n : ℝ) < 1 by rw [hn']; norm_num)
    omega

example :
    ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv.symm cubicCharacter =
      Additive.ofMul cubicMonoidCharacter := by
  exact ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv.symm_apply_apply _

example {A : Type u} [AddMonoid A] {B : Type v} [AddMonoid B]
    (χ : A →+ AddCircle (1 : ℚ)) (f : B →+ A) :
    (AddCircle.continuousAddEquivCircle one_ne_zero).toAddEquiv.toAddMonoidHom.comp
        ((AddCircle.rationalToReal.comp χ).comp f) =
      AddCircle.rationalToCircle.comp (χ.comp f) := by
  rw [← AddMonoidHom.comp_assoc, ← AddMonoidHom.comp_assoc,
    AddCircle.continuousAddEquivCircle_comp_rationalToReal]
  exact AddMonoidHom.comp_assoc _ _ _
