/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Data.DFinsupp.Defs

/-!
# Pointwise multiplication of dependent finitely supported functions

`DFinsupp.pointwiseMul` multiplies dependent finitely supported functions coordinatewise.
It is a named `Mul` datum, not an instance: its multiplication is selected explicitly,
without changing the multiplication used for graded direct sums.

The product is characterized by its values and coercion to a dependent function. Products of
singles at different indices vanish, and the support of a product is contained in the
intersection of the supports. No multiplicative associativity or unit is required.

## References

This construction generalizes Mathlib's `Mathlib.Data.Finsupp.Pointwise`, by Kim Morrison,
using the dependent finitely supported function API of Johannes Hölzl and Kenny Lau.
-/

@[expose] public section

universe u v

namespace DFinsupp

variable {ι : Type u} {β : ι → Type v} [∀ i, MulZeroClass (β i)]

/-- Pointwise multiplication of dependent finitely supported functions.

This is not registered as an instance, so it can be selected without affecting other
multiplications on the same carrier. -/
@[instance_reducible]
def pointwiseMul : Mul (Π₀ i, β i) where
  mul := zipWith (fun _ => (· * ·)) (fun _ => mul_zero 0)

/-- Evaluation of the pointwise product is multiplication in the corresponding fibre. -/
@[simp]
theorem pointwiseMul_apply (x y : Π₀ i, β i) (i : ι) :
    (@Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) x y) i = x i * y i :=
  zipWith_apply _ _ x y i

/-- Coercion of the pointwise product to a dependent function is coordinatewise multiplication. -/
theorem coe_pointwiseMul (x y : Π₀ i, β i) :
    ⇑(@Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) x y) = ⇑x * ⇑y := by
  funext i
  rw [pointwiseMul_apply, Pi.mul_apply]

section Single

variable [DecidableEq ι]

/-- A single supported at one index sends a fibre product to the pointwise product of singles. -/
@[simp]
theorem single_pointwiseMul (i : ι) (a b : β i) :
    single i (a * b) =
      @Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) (single i a) (single i b) :=
  (zipWith_single_single (fun _ => (· * ·)) (fun _ => mul_zero 0) a b).symm

/-- Singles at distinct indices have zero pointwise product. -/
@[simp]
theorem pointwiseMul_single_single_of_ne {i j : ι} (hij : i ≠ j) (a : β i) (b : β j) :
    @Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) (single i a) (single j b) = 0 := by
  apply DFinsupp.ext
  intro k
  by_cases hki : k = i
  · subst k
    rw [pointwiseMul_apply, single_eq_of_ne hij, mul_zero, zero_apply]
  · rw [pointwiseMul_apply, single_eq_of_ne hki, zero_mul, zero_apply]

end Single

section Support

variable [DecidableEq ι] [∀ i (a : β i), Decidable (a ≠ 0)]

/-- The support of a pointwise product is contained in the support of its left factor. -/
theorem support_pointwiseMul_subset_left {x y : Π₀ i, β i} :
    (@Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) x y).support ⊆ x.support := by
  intro i hi
  apply mem_support_iff.mpr
  intro hxi
  apply (mem_support_iff.mp hi)
  rw [pointwiseMul_apply, hxi, zero_mul]

/-- The support of a pointwise product is contained in the support of its right factor. -/
theorem support_pointwiseMul_subset_right {x y : Π₀ i, β i} :
    (@Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) x y).support ⊆ y.support := by
  intro i hi
  apply mem_support_iff.mpr
  intro hyi
  apply (mem_support_iff.mp hi)
  rw [pointwiseMul_apply, hyi, mul_zero]

/-- The support of a pointwise product is contained in the intersection of the supports. -/
theorem support_pointwiseMul {x y : Π₀ i, β i} :
    (@Mul.mul (Π₀ i, β i) (pointwiseMul (β := β)) x y).support ⊆ x.support ∩ y.support :=
  Finset.subset_inter support_pointwiseMul_subset_left support_pointwiseMul_subset_right

end Support

end DFinsupp
