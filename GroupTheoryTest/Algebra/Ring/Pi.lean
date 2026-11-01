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

Unital maps from a finite power of ℕ to ℕ are evaluations at unique
coordinates, by unit-coordinate selection and multiplicative recovery.
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

-- Every unital map from a finite power of ℕ to ℕ is evaluation at a unique coordinate.
example {ι : Type u} [Finite ι] (f : (ι → ℕ) →+* ℕ) :
    ∃! i : ι, ∀ x : ι → ℕ, f x = x i := by
  classical
  obtain ⟨i, hi, huniq⟩ := RingHomClass.existsUnique_map_single_one_eq_one f
  have hcoordinate (x : ι → ℕ) : f x = x i := by
    calc
      f x = f (Pi.single i (x i)) := by
        simpa only [hi, one_mul] using MulHomClass.single_one_mul_apply f i x
      _ = f (fun _ : ι => x i) := by
        simpa only [hi, one_mul] using
          (MulHomClass.single_one_mul_apply f i (fun _ : ι => x i)).symm
      _ = x i := map_natCast f (x i)
  refine ⟨i, hcoordinate, ?_⟩
  intro j hj
  apply huniq j
  simpa using hj (Pi.single j (1 : ℕ))
