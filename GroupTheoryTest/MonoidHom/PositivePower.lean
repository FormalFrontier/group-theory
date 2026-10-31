/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.MonoidHom.PositivePower

/-!
# Equality of functions from finite power comparisons

A finite family of powers with gcd one detects equality of functions pointwise, without
commutativity or unique-root assumptions on the codomain.
-/

universe u v w

example {ι : Type u} {X : Type v} {T : Type w} [LeftCancelMonoid T]
    (s : Finset ι) (e : ι → ℕ) (hg : s.gcd e = 1) (f g : X → T)
    (h : ∀ i ∈ s, ∀ x, f x ^ (e i) = g x ^ (e i)) : f = g := by
  funext x
  exact Finset.eq_of_forall_pow_eq_of_gcd_eq_one hg (fun i hi => h i hi x)
