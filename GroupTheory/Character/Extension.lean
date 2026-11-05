/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Extension of circle-valued characters

A homomorphism from a subgroup of a commutative group to the complex unit circle
extends to the whole group. This is an algebraic extension theorem: it requires
no topology on the domain and makes no continuity or uniqueness assertion.

The proof transports divisibility along the surjective exponential homomorphism
and applies Baer's criterion over `ℤ`, followed by the module extension property.

## References

* Mathlib's `Module.Baer.of_divisible` and `Module.Injective.extension_property`.
-/

@[expose] public section

private noncomputable instance circleDivisible : DivisibleBy (Additive Circle) ℤ :=
  Function.Surjective.divisibleBy (f := Circle.expHom)
    (show Function.Surjective Circle.expHom from Circle.exp_surjective)
    (fun x n => map_zsmul Circle.expHom n x)

private instance circleInjective : Module.Injective ℤ (Additive Circle) :=
  (Module.Baer.of_divisible (Additive Circle)).injective

universe u

variable {A : Type u} [CommGroup A]

/-- Every circle-valued character of a subgroup of a commutative group extends to
its ambient group. No topology on the domain is required. -/
theorem MonoidHom.exists_extend_circle
    (H : Subgroup A) (f : H →* Circle) :
    ∃ g : A →* Circle, g.comp H.subtype = f := by
  let i := H.subtype.toAdditive.toIntLinearMap
  let f' := f.toAdditive.toIntLinearMap
  obtain ⟨g, hg⟩ := Module.Injective.extension_property ℤ (Additive Circle)
    (Additive H) (Additive A) i (by
      intro x y h
      exact Subtype.ext h) f'
  refine ⟨MonoidHom.toAdditive.symm g.toAddMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  exact LinearMap.congr_fun hg (Additive.ofMul x)
