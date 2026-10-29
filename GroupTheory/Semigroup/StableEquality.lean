/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Right-stabilized image equality and reflection

For right-cofinal homomorphisms, equality after right multiplication by a common
target element is equivalent to equality of images after right multiplication by
a common source element. Injective right-cofinal homomorphisms reflect equality
after right stabilization. No identity or commutativity is required.

These statements supply the stabilization step in cofinality arguments for
additive Grothendieck completions, without a unit or commutativity hypothesis.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-Theory* (2013),
  for background on additive Grothendieck completions.
-/

@[expose] public section

universe u v w

namespace MulHomClass

variable {M : Type u} {N : Type v} {F : Type w}
variable [Mul M] [Semigroup N] [FunLike F M N] [MulHomClass F M N]

/-- For a right-cofinal homomorphism, right-stabilized equality of images is equivalent to
equality of images after a common right multiplication in the source.
The source needs only multiplication; associativity is used only in the target. -/
@[to_additive]
theorem exists_mul_right_eq_iff_exists_map_eq
    (f : F) (hcof : ∀ b : N, ∃ a : M, ∃ c : N, b * c = f a) (x y : M) :
    (∃ t : N, f x * t = f y * t) ↔ ∃ a : M, f (x * a) = f (y * a) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨a, c, hc⟩ := hcof t
    refine ⟨a, ?_⟩
    calc
      f (x * a) = (f x * t) * c := by rw [map_mul, ← hc, mul_assoc]
      _ = (f y * t) * c := congrArg (· * c) ht
      _ = f (y * a) := by rw [map_mul, ← hc, mul_assoc]
  · rintro ⟨a, ha⟩
    exact ⟨f a, by simpa only [map_mul] using ha⟩

/-- Right-cofinal injective homomorphisms reflect equality after right stabilization.
The source needs only multiplication; associativity is used only in the target. -/
@[to_additive]
theorem exists_mul_right_eq_iff
    (f : F) (hf : Function.Injective f)
    (hcof : ∀ b : N, ∃ a : M, ∃ c : N, b * c = f a) (x y : M) :
    (∃ t : N, f x * t = f y * t) ↔ ∃ a : M, x * a = y * a := by
  refine (exists_mul_right_eq_iff_exists_map_eq f hcof x y).trans ?_
  exact ⟨fun ⟨a, ha⟩ => ⟨a, hf ha⟩, fun ⟨a, ha⟩ => ⟨a, congrArg f ha⟩⟩

end MulHomClass
