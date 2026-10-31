/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.MonoidHom.PositivePower

/-!
# Equality of functions from finite power comparisons

A finite family of powers with gcd one detects equality of functions pointwise, without
commutativity or unique-root assumptions on the codomain. Only the first function's
values must be left-regular; the additive criterion has the same pointwise application.
-/

universe u v w

example {ι : Type u} {X : Type v} {T : Type w} [Monoid T]
    (s : Finset ι) (e : ι → ℕ) (hg : s.gcd e = 1) (f g : X → T)
    (hf : ∀ x, IsLeftRegular (f x))
    (h : ∀ i ∈ s, ∀ x, f x ^ (e i) = g x ^ (e i)) : f = g := by
  funext x
  exact (hf x).eq_of_forall_pow_eq_of_gcd_eq_one hg (fun i hi => h i hi x)

example {ι : Type u} {X : Type v} {T : Type w} [AddMonoid T]
    (s : Finset ι) (e : ι → ℕ) (hg : s.gcd e = 1) (f g : X → T)
    (hf : ∀ x, IsAddLeftRegular (f x))
    (h : ∀ i ∈ s, ∀ x, e i • f x = e i • g x) : f = g := by
  funext x
  exact (hf x).eq_of_forall_nsmul_eq_of_gcd_eq_one hg (fun i hi => h i hi x)
