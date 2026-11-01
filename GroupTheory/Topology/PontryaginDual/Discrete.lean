/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.PontryaginDual
import GroupTheory.Topology.RationalCircleCharacter
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Injectivity of bidual evaluation for discrete commutative groups

Rational-circle characters detect nonzero differences in the additive view of a commutative
group. Composing a detecting character with `AddCircle.rationalToCircle` gives a circle-valued
character. Discreteness makes this character continuous, so the evaluation application law
shows that bidual evaluation separates the original group elements.

## References

The proof uses the existing `CharacterModule.exists_character_apply_ne_zero_of_ne_zero`
interface and the rational-circle embedding `AddCircle.rationalToCircle`. The group, type-tag,
and continuous-homomorphism infrastructure is provided by Mathlib.
-/

@[expose] public section

universe u

namespace PontryaginDual

/-- Bidual evaluation is injective on a discrete commutative group. -/
theorem eval_injective_of_discrete (G : Type u) [CommGroup G]
    [TopologicalSpace G] [DiscreteTopology G] :
    Function.Injective (PontryaginDual.eval G) := by
  classical
  intro g h hEval
  by_contra hgh
  have hd : Additive.ofMul g - Additive.ofMul h ≠ 0 := by
    intro hd
    apply hgh
    simpa only [toMul_ofMul] using
      congrArg Additive.toMul (sub_eq_zero.mp hd)
  obtain ⟨c, hc⟩ : ∃ c : Additive G →+ AddCircle (1 : ℚ),
      c (Additive.ofMul g - Additive.ofMul h) ≠ 0 := by
    apply CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    exact hd
  let θ : PontryaginDual G :=
    { toFun := fun x ↦ Additive.toMul
        (AddCircle.rationalToCircle (Multiplicative.ofAdd (c (Additive.ofMul x))))
      map_one' := by
        change Additive.toMul
          (AddCircle.rationalToCircle (c (0 : Additive G))) = 1
        rw [_root_.map_zero, _root_.map_zero, toMul_zero]
      map_mul' := by
        intro x y
        change Additive.toMul
          (AddCircle.rationalToCircle (c (Additive.ofMul x + Additive.ofMul y))) =
          Additive.toMul (AddCircle.rationalToCircle (c (Additive.ofMul x))) *
            Additive.toMul (AddCircle.rationalToCircle (c (Additive.ofMul y)))
        rw [_root_.map_add, _root_.map_add, toMul_add]
      continuous_toFun := continuous_of_discreteTopology }
  have hθ_apply (x : G) : θ x = Additive.toMul
      (AddCircle.rationalToCircle (Multiplicative.ofAdd (c (Additive.ofMul x)))) := rfl
  have hθ : θ g = θ h := by
    have he := congrArg (fun F : PontryaginDual (PontryaginDual G) ↦ F θ) hEval
    simpa only [PontryaginDual.eval_apply] using he
  have hcoeff : c (Additive.ofMul g) = c (Additive.ofMul h) := by
    apply AddCircle.rationalToCircle_injective
    change AddCircle.rationalToCircle (Multiplicative.ofAdd (c (Additive.ofMul g))) =
      AddCircle.rationalToCircle (Multiplicative.ofAdd (c (Additive.ofMul h)))
    simpa only [hθ_apply, ofMul_toMul] using
      congrArg (Additive.ofMul : Circle → Additive Circle) hθ
  apply hc
  rw [_root_.map_sub, hcoeff, sub_self]

end PontryaginDual
