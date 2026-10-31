/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.Order.Ring.MulHom
public import GroupTheory.Algebra.Order.Ring.Sign
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Squares in finite integer-valued multiplicative images
-/

@[expose] public section

universe u

namespace MulHom

variable {M : Type u} [Mul M]

/-- Squares in a finite integer-valued multiplicative image are zero or one. -/
theorem map_self_mul_eq_zero_or_one_of_finite_range (f : M →ₙ* ℤ)
    (hfinite : (Set.range f).Finite) (x : M) :
    f (x * x) = 0 ∨ f (x * x) = 1 := by
  rw [map_mul]
  rcases MulHomClass.map_eq_zero_or_one_or_neg_one_of_finite_range f hfinite x
    with h | h | h <;> simp [h]

end MulHom

example {M : Type*} {R : Type*} [Mul M] [NonUnitalNonAssocRing R]
    [LinearOrder R] [IsOrderedAddMonoid R] [PosMulStrictMono R]
    (f : M →ₙ* R) (a b : M) :
    SignType.sign (f (a * b)) = SignType.sign (f a) * SignType.sign (f b) := by
  rw [map_mul]
  exact map_mul (SignType.signMulHom (α := R)) (f a) (f b)
