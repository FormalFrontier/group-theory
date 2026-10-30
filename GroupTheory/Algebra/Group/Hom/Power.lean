/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.NatPowAssoc

/-!
# Natural powers under multiplicative maps

A multiplication-preserving map need not preserve one. Its value at one is nevertheless an
idempotent and a two-sided identity on its image. With power-associative natural powers, such a
map preserves positive powers, and its value at every natural power is obtained by multiplying
the corresponding target power on the left by the image of one.

## Main results

* `MulHomClass.apply_one_mul_apply` and `MulHomClass.apply_mul_apply_one`: the image of one
  acts as an identity on the image, even when the target has only multiplication.
* `MulHomClass.map_pow_of_ne_zero`: multiplicative maps preserve positive natural powers.
* `MulHomClass.map_pow_eq_apply_one_mul`: the image of one accounts for exponent zero.
* `MulHomClass.map_pow_mul`: a mixed-product formula valid at every natural exponent.
* `MulHomClass.map_pow_mul_of_apply_eq_apply_one`: the mixed-product formula when the second
  factor has the same image as one.
* `MulHomClass.map_pow_of_map_one`: a genuine one-preservation hypothesis removes the
  leading factor at every exponent.

## Relation to `map_pow`

Mathlib's `map_pow` applies to unital maps between monoids. The results here generalize both
its one-preservation and associativity assumptions: they use `MulHomClass` and the stock
`NatPowAssoc` laws, without associativity of arbitrary products. Under the hypotheses of
`map_pow`, supplying `map_one f` to `MulHomClass.map_pow_of_map_one` recovers the same
all-natural preservation statement. Existing unital APIs are unchanged.

## Implementation notes

The single preservation induction starts at exponent one. Positive powers of image elements
are again images, so the image-unit identities apply to them. The ambient target unit, which
is the zeroth power, need not lie in the image. No reassociation or commutation of arbitrary
products is needed.

## References

The multiplicative-map interface and unital power-preservation API are from Mathlib's
`Mathlib.Algebra.Group.Hom.Defs`. The stock power-associativity interface is due to
Scott Carnahan in `Mathlib.Algebra.Group.NatPowAssoc`.
-/

@[expose] public section

universe u v w

namespace MulHomClass

variable {M : Type u} {N : Type v} {F : Type w}

section ImageOne

variable [MulOneClass M] [Mul N] [FunLike F M N] [MulHomClass F M N]

/-- The image of one is a left identity on the image of a multiplicative map. -/
@[simp]
theorem apply_one_mul_apply (f : F) (x : M) : f 1 * f x = f x := by
  rw [← _root_.map_mul, one_mul]

/-- The image of one is a right identity on the image of a multiplicative map. -/
@[simp]
theorem apply_mul_apply_one (f : F) (x : M) : f x * f 1 = f x := by
  rw [← _root_.map_mul, mul_one]

/-- The image of one under a multiplicative map is idempotent. -/
theorem apply_one_mul_apply_one (f : F) : f 1 * f 1 = f 1 :=
  apply_one_mul_apply f 1

end ImageOne

section Powers

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]
variable [MulOneClass N] [Pow N ℕ] [NatPowAssoc N]
variable [FunLike F M N] [MulHomClass F M N]

/-- A multiplicative map preserves every positive natural power, without preserving one. -/
theorem map_pow_of_ne_zero (f : F) (a : M) (n : ℕ) (hn : n ≠ 0) :
    f (a ^ n) = (f a) ^ n := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    clear hn
    -- Induction on the predecessor starts at exponent one.
    induction n with
    | zero => exact (congrArg f (npow_one a)).trans (npow_one (f a)).symm
    | succ n ih =>
      rw [npow_add (n + 1) 1 a, npow_one, _root_.map_mul, ih,
        npow_add (n + 1) 1 (f a), npow_one]

/-- Multiplication by the image of one gives the image of every natural power, including zero. -/
theorem map_pow_eq_apply_one_mul (f : F) (a : M) (n : ℕ) :
    f (a ^ n) = f 1 * (f a) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp only [npow_zero, mul_one]
  · calc
      f (a ^ n) = f 1 * f (a ^ n) := (apply_one_mul_apply f (a ^ n)).symm
      _ = f 1 * (f a) ^ n := by rw [map_pow_of_ne_zero f a n hn]

/-- A multiplicative map separates a natural power from a following factor, even at zero. -/
theorem map_pow_mul (f : F) (a b : M) (n : ℕ) :
    f (a ^ n * b) = (f a) ^ n * f b := by
  by_cases hn : n = 0
  · subst n
    simp only [npow_zero, one_mul]
  · rw [_root_.map_mul, map_pow_of_ne_zero f a n hn]

/-- If the second factor has the image of one, a mixed product has the leading image-unit
formula at every natural exponent. -/
theorem map_pow_mul_of_apply_eq_apply_one
    (f : F) (a b : M) (n : ℕ) (hy : f b = f 1) :
    f (a ^ n * b) = f 1 * (f a) ^ n := by
  by_cases hn : n = 0
  · subst n
    simpa only [npow_zero, one_mul, mul_one] using hy
  · calc
      f (a ^ n * b) = (f a) ^ n * f b := map_pow_mul f a b n
      _ = f (a ^ n) * f 1 := by rw [← map_pow_of_ne_zero f a n hn, hy]
      _ = f (a ^ n) := apply_mul_apply_one f (a ^ n)
      _ = f 1 * (f a) ^ n := map_pow_eq_apply_one_mul f a n

/-- A multiplicative map that genuinely preserves one preserves all natural powers.

For monoids and a `MonoidHomClass`, taking `h1 := map_one f` recovers the statement of
Mathlib's `map_pow f a n`, also exposed as `MonoidHom.map_pow` for bundled monoid maps. -/
theorem map_pow_of_map_one (f : F) (h1 : f (1 : M) = (1 : N)) (a : M) (n : ℕ) :
    f (a ^ n) = (f a) ^ n := by
  rw [map_pow_eq_apply_one_mul f a n, h1, one_mul]

end Powers

end MulHomClass
