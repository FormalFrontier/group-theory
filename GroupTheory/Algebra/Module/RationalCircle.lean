/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Extension of rational-circle characters

Additive homomorphisms to the rational circle extend along injective additive
homomorphisms of additive commutative groups, with independent source universes.

## References

The proof uses Mathlib's `Module.Injective.extension_property` and the canonical
integer-module structure of an additive commutative group.
-/

@[expose] public section

universe u v

namespace AddCircle

/-- Every additive homomorphism to the rational circle extends along an injective
additive homomorphism of additive commutative groups.

The proof uses Mathlib's extension property for injective integer modules. -/
theorem exists_addMonoidHom_extension
    {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f)
    (φ : A →+ AddCircle (1 : ℚ)) :
    ∃ ψ : B →+ AddCircle (1 : ℚ), ψ.comp f = φ := by
  have : Module.Injective ℤ (AddCircle (1 : ℚ)) :=
    (Module.Baer.of_divisible (AddCircle (1 : ℚ))).injective
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property
    (R := ℤ) (M := AddCircle (1 : ℚ)) (P := A) (P' := B)
    f.toIntLinearMap hf φ.toIntLinearMap
  refine ⟨ψ.toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro a
  exact LinearMap.congr_fun hψ a

end AddCircle
