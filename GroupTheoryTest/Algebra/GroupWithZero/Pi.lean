/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Algebra.GroupWithZero.Pi
import GroupTheory.Ring.Hom.FiniteSum

/-!
# Injectivity of finite-product ring lifts

The generic multiplicative-map criterion recovers injectivity of
`Pi.liftRingHom` from injectivity of its nonunital component maps. This uses the
existing single-extension law at the nonassociative-semiring fibre and semiring
target level. Decidable equality is chosen only inside the proof.
-/

universe u v w

open scoped BigOperators

example {ι : Type u} {R : ι → Type v} {S : Type w}
    [∀ i, NonAssocSemiring (R i)] [Semiring S] [Fintype ι]
    (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) :
    Function.Injective (Pi.liftRingHom φ horth hone) ↔
      ∀ i, Function.Injective (φ i) := by
  classical
  simpa only [Pi.liftRingHom_single] using
    (MulHomClass.injective_iff_comp_single (Pi.liftRingHom φ horth hone))
