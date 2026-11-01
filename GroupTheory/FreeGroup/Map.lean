/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Logic.Function.Basic

/-!
# Kernels, injectivity and surjectivity of maps between free groups

The homomorphism `FreeGroup.map f` is injective or surjective exactly when its generator map
`f` has the corresponding property. The generator types may lie in independent universes and
need not be finite or nonempty. The kernel is the normal closure of the differences
`of i * (of k)⁻¹` of generators with the same image (`FreeGroup.ker_map`).

Injectivity is detected on generators. Surjectivity is detected by sending a generator outside
the image to the generator of `FreeGroup Unit`, and every other generator to the identity.
The reverse implications reuse Mathlib's `FreeGroup.map_injective` and
`FreeGroup.map_surjective`.

For the kernel formula, quotient by the normal closure of the equal-label differences.
The quotient generator assignment is constant on label fibers, so `Function.extend` extends
it to all target labels, taking the identity outside the image. The free-group universal
property then factors the quotient map through `FreeGroup.map`.

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

/-- The kernel of a generator relabeling is the normal closure of differences of generators
with the same label. The generator universes are independent, and the label map need not be
surjective. -/
theorem ker_map {I : Type u} {J : Type v} (σ : I → J) :
    (FreeGroup.map σ).ker =
      Subgroup.normalClosure
        {g : FreeGroup I | ∃ i k : I,
          σ i = σ k ∧ g = FreeGroup.of i * (FreeGroup.of k)⁻¹} := by
  let N := Subgroup.normalClosure
    {g : FreeGroup I | ∃ i k : I, σ i = σ k ∧ g = of i * (of k)⁻¹}
  let q := QuotientGroup.mk' N
  have hf : (fun i : I => q (of i)).FactorsThrough σ := by
    intro i k h
    have hrel : of i * (of k)⁻¹ ∈ N :=
      Subgroup.subset_normalClosure ⟨i, k, h, rfl⟩
    have hqrel : q (of i * (of k)⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 hrel
    exact mul_inv_eq_one.mp (by simpa only [_root_.map_mul, _root_.map_inv] using hqrel)
  -- Values outside the label map's image can be chosen to be the identity.
  let φ := lift (Function.extend σ (fun i : I => q (of i)) (fun _ => 1))
  have hq : φ.comp (FreeGroup.map σ) = q := by
    apply ext_hom
    intro i
    simpa only [φ, MonoidHom.comp_apply, map.of, lift_apply_of] using
      hf.extend_apply (fun _ => 1) i
  change (FreeGroup.map σ).ker = N
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    change FreeGroup.map σ x = 1 at hx
    have he : φ (FreeGroup.map σ x) = q x := DFunLike.congr_fun hq x
    exact he.symm.trans (by rw [hx, _root_.map_one])
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨i, k, h, rfl⟩
    change FreeGroup.map σ (of i * (of k)⁻¹) = 1
    rw [_root_.map_mul, _root_.map_inv, map.of, map.of, h, mul_inv_cancel]

end FreeGroup
