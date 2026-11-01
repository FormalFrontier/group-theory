/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.GroupWithZero.Pi

/-!
# Coordinate detection for multiplicative maps out of products

A multiplicative map from a dependent product of `MulZeroOneClass` types can be
studied by restricting it to the zero-off coordinate insertions `Pi.single`.
Multiplication by the image of `Pi.single i 1`, on either side, recovers the
image of the insertion of the `i`th coordinate. Consequently, injectivity and
one-way zero reflection are each detected by the coordinate restrictions.

## Main results

* `MulHomClass.single_one_mul_apply` and `MulHomClass.apply_mul_single_one`
  recover the image of a single coordinate by multiplication on the left and
  on the right, respectively.
* `MulHomClass.injective_iff_comp_single` characterizes injectivity by
  injectivity on every zero-off coordinate insertion.
* `MulHomClass.reflects_zero_iff_comp_single` characterizes one-way zero
  reflection by the corresponding property of every coordinate restriction.

## Implementation notes

The index type need not be finite. The fibres need not have associative
multiplication, and the target needs only multiplication for recovery and
injectivity. The zero-reflection criterion additionally uses zero and its
absorbing laws in the target. No preservation of zero or one is assumed.
In particular, one-way zero reflection does not assert `f x = 0 ↔ x = 0`.
Decidable equality is used only for the stock `Pi.single` notation.

## References

The proofs use Mathlib's `map_mul`, `Pi.single_mul_left`,
`Pi.single_mul_right` and `Pi.single_eq_same` APIs.
-/

@[expose] public section

universe u v w z

namespace MulHomClass

variable {ι : Type u} {R : ι → Type v} {S : Type w} {F : Type z}
variable [DecidableEq ι] [∀ i, MulZeroOneClass (R i)]

section Mul

variable [Mul S] [FunLike F (∀ i, R i) S] [MulHomClass F (∀ i, R i) S]

/-- Multiplying the image of a product element on the left by the image of the
unit supported at `i` recovers the image of its `i`th coordinate insertion.
The map need only preserve multiplication, and the target need not have a unit
or associative multiplication. -/
theorem single_one_mul_apply (f : F) (i : ι) (x : ∀ i, R i) :
    f (Pi.single i 1) * f x = f (Pi.single i (x i)) := by
  rw [← map_mul, ← Pi.single_mul_left, one_mul]

/-- Multiplying the image of a product element on the right by the image of the
unit supported at `i` recovers the image of its `i`th coordinate insertion.
Together with `single_one_mul_apply`, this shows that the supported unit image
commutes with every value of the map, not necessarily with the whole target. -/
theorem apply_mul_single_one (f : F) (i : ι) (x : ∀ i, R i) :
    f x * f (Pi.single i 1) = f (Pi.single i (x i)) := by
  rw [← map_mul, ← Pi.single_mul_right, mul_one]

/-- A multiplicative map out of a dependent product is injective if and only if
its restriction to every zero-off coordinate insertion is injective.
The index type may be infinite or empty; neither finiteness nor preservation
of zero or one is required. -/
theorem injective_iff_comp_single (f : F) :
    Function.Injective f ↔
      ∀ i, Function.Injective (fun a : R i => f (Pi.single i a)) := by
  constructor
  · intro hf i a b hab
    have h := congrArg (fun x : ∀ j, R j => x i) (hf hab)
    simpa only [Pi.single_eq_same] using h
  · intro hf x y hxy
    funext i
    apply hf i
    change f (Pi.single i (x i)) = f (Pi.single i (y i))
    rw [← single_one_mul_apply f i x, ← single_one_mul_apply f i y, hxy]

end Mul

section MulZero

variable [MulZeroClass S] [FunLike F (∀ i, R i) S]
    [MulHomClass F (∀ i, R i) S]

/-- A multiplicative map out of a dependent product reflects zero if and only if
every zero-off coordinate restriction reflects zero. Here reflection is the
one-way property `f x = 0 → x = 0`, not an equivalence: the map is not assumed
to preserve zero. The statement also includes empty products. -/
theorem reflects_zero_iff_comp_single (f : F) :
    (∀ x : ∀ i, R i, f x = 0 → x = 0) ↔
      ∀ i (a : R i), f (Pi.single i a) = 0 → a = 0 := by
  constructor
  · intro hf i a ha
    have h := congrArg (fun x : ∀ j, R j => x i) (hf (Pi.single i a) ha)
    simpa using h
  · intro hf x hx
    funext i
    apply hf i (x i)
    rw [← single_one_mul_apply f i x, hx, mul_zero]

end MulZero

end MulHomClass
