/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Ring.Hom.FiniteSum
import Mathlib.Algebra.Ring.Prod

/-!
# A two-coordinate use of the finite-product lift

The two zero-off component maps into `R × R` recover the two coordinates.
Only `Semiring R` is required, so the example also applies to noncommutative
semirings.
-/

@[expose] public section

universe u

example {R : Type u} [Semiring R] (x : Bool → R) :
    Pi.liftRingHom
      (fun b : Bool =>
        if b then (0 : R →ₙ+* R).prod (NonUnitalRingHom.id R)
        else (NonUnitalRingHom.id R).prod (0 : R →ₙ+* R))
      (by
        intro i j hij
        cases i <;> cases j <;> simp_all)
      (by
        ext <;> simp)
      x = (x false, x true) := by
  simp [Pi.liftRingHom_apply]
