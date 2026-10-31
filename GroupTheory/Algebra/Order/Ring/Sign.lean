/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Basic.Sign.Basic

/-!
# Multiplicativity of the sign function

Positive left multiplication being strictly increasing suffices for signs to
multiply, without a unit or associativity.
-/

@[expose] public section

universe u

namespace SignType

variable {α : Type u}

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α] [LinearOrder α] [IsOrderedAddMonoid α]
  [PosMulStrictMono α]

/-- Multiplicativity of signs without a unit or associativity. -/
theorem sign_mul (a b : α) : sign (a * b) = sign a * sign b := by
  have hp (x : α) (hx : 0 < x) (y : α) : sign (x * y) = sign y := by
    let f : ZeroHom α α := ⟨(x * ·), mul_zero x⟩
    exact StrictMono.sign_comp (f := f)
      (fun _ _ h => mul_lt_mul_of_pos_left h hx) y
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h := hp (-a) (neg_pos.mpr ha) b
    rw [neg_mul, Left.sign_neg] at h
    rw [sign_neg ha]
    simpa using congrArg Neg.neg h
  · simp [ha]
  · rw [sign_pos ha, one_mul]
    exact hp a ha b

/-- The sign function as a nonunital multiplicative homomorphism. -/
def signMulHom : α →ₙ* SignType where
  toFun := sign
  map_mul' := sign_mul

/-- Evaluation of the nonunital sign map. -/
@[simp] theorem signMulHom_apply (a : α) : signMulHom a = sign a := rfl

end NonUnitalNonAssocRing

section StrictOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The nonunital sign map agrees pointwise with the unital sign map. -/
theorem signMulHom_apply_eq_signHom (a : α) : signMulHom a = signHom a := rfl

end StrictOrderedRing

end SignType
