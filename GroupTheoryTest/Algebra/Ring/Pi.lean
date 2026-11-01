/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Algebra.Ring.Pi
import GroupTheory.Ring.Hom.FiniteSum

/-!
# Zero images under finite-product lifts

The finite lift of an orthogonal family of nonunital ring homomorphisms vanishes
at an element exactly when every component value vanishes. This uses the generic
finite-support criterion and the lift's coordinate restriction API.
-/

@[expose] public section

universe u v w

open scoped BigOperators

example {ι : Type u} {R : ι → Type v} {S : Type w}
    [∀ i, NonAssocSemiring (R i)] [Semiring S] [Fintype ι]
    (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) (x : ∀ i, R i) :
    Pi.liftRingHom φ horth hone x = 0 ↔ ∀ i, φ i (x i) = 0 := by
  classical
  simpa only [Pi.liftRingHom_single] using
    NonUnitalRingHomClass.map_eq_zero_iff_single_of_finite_support
      (Pi.liftRingHom φ horth hone) x (Set.toFinite _)
