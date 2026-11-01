/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Algebra.Divisibility.Basic

/-!
# Power divisibility in commutative monoids

The elementwise commuting theorem gives the usual power-divisibility conclusion under
commutative-monoid assumptions.
-/

universe u

example {M : Type u} [CommMonoid M] {a c : M} (hdvd : a ∣ c) (n : ℕ) :
    a ^ n ∣ c ^ n :=
  Commute.pow_dvd_pow_of_dvd (Commute.all a c) hdvd n
