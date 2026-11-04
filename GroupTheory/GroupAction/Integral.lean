/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Finite orbits of integral elements

An element integral over a commutative ring has a finite orbit under a scalar-commuting
monoid action by semiring endomorphisms on a commutative domain.

## References

Mathlib's `IsIntegral`, `Polynomial.Monic.mem_rootSet`, `Polynomial.smul_mem_rootSet`,
and `Polynomial.rootSet_finite` provide the integrality and finite-root APIs.
-/

@[expose] public section

universe u v w

/-- An integral element of a commutative domain has finite orbit under a monoid action
by semiring endomorphisms commuting with the base scalars. -/
theorem IsIntegral.finite_orbit
    {R : Type u} {A : Type v} {M : Type w}
    [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]
    {x : A} (hx : IsIntegral R x) : (MulAction.orbit M x).Finite := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hxroot : x ∈ p.rootSet A := hp.mem_rootSet.mpr hpx
  refine (Polynomial.rootSet_finite p A).subset ?_
  rintro y ⟨m, rfl⟩
  exact Polynomial.smul_mem_rootSet m hxroot
