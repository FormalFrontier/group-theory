/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Injectivity and surjectivity of maps between free groups

The homomorphism `FreeGroup.map f` is injective or surjective exactly when its generator map
`f` has the corresponding property. The generator types may lie in independent universes and
need not be finite or nonempty.

Injectivity is detected on generators. Surjectivity is detected by sending a generator outside
the image to the generator of `FreeGroup Unit`, and every other generator to the identity.
The reverse implications reuse Mathlib's `FreeGroup.map_injective` and
`FreeGroup.map_surjective`.

## References

- Mathlib's free-group construction and map API, formalized by Kenny Lau.
-/

@[expose] public section

universe u v

namespace FreeGroup

variable {α : Type u} {β : Type v}

/-- The induced homomorphism of free groups is injective exactly when its generator map is. -/
@[simp]
theorem map_injective_iff (f : α → β) :
    Function.Injective (FreeGroup.map f) ↔ Function.Injective f := by
  constructor
  · intro h a a' haa'
    apply of_injective
    apply h
    simpa only [map.of] using congrArg (of : β → FreeGroup β) haa'
  · exact map_injective

/-- The induced homomorphism of free groups is surjective exactly when its generator map is. -/
@[simp]
theorem map_surjective_iff (f : α → β) :
    Function.Surjective (FreeGroup.map f) ↔ Function.Surjective f := by
  classical
  constructor
  · intro h b
    by_contra hb
    have hf (a : α) : f a ≠ b := fun ha => hb ⟨a, ha⟩
    let χ : FreeGroup β →* FreeGroup Unit :=
      lift (fun c => if c = b then of Unit.unit else 1)
    have hχ : χ.comp (FreeGroup.map f) = 1 := by
      apply ext_hom
      intro a
      simp [χ, hf a]
    obtain ⟨x, hx⟩ := h (of b)
    apply of_ne_one Unit.unit
    calc
      of Unit.unit = χ (of b) := by simp [χ]
      _ = χ (FreeGroup.map f x) := congrArg χ hx.symm
      _ = 1 := by
        simpa only [MonoidHom.comp_apply, MonoidHom.one_apply] using
          DFunLike.congr_fun hχ x
  · exact map_surjective

end FreeGroup
