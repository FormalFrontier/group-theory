/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite kernels and fibers

A homomorphism from a group to a type with multiplication and identity has finite fibers exactly
when its kernel is finite. The target only needs `MulOneClass`: neither associativity nor inverses
are required. The additive statement applies to arbitrary, possibly noncommutative additive groups
and targets with `AddZeroClass`.

## Implementation notes

An occupied fiber injects into the kernel by division by a fixed element of that fiber. This uses
the source group operations and Mathlib's `MonoidHom.div_mem_ker_iff`; empty fibers are finite.
The converse identifies the kernel with the fiber at the identity using `MonoidHom.coe_ker`.
-/

@[expose] public section

universe u v

namespace MonoidHom

/-- A homomorphism from a group to a type with multiplication and identity has finite kernel
if and only if all its fibers are finite. -/
@[to_additive /-- A homomorphism from an additive group to a type with addition and zero has finite
kernel if and only if all its fibers are finite. -/]
theorem finite_ker_iff_finite_fibers {G : Type u} {M : Type v} [Group G] [MulOneClass M]
    (f : G →* M) : Finite f.ker ↔ ∀ y : M, (f ⁻¹' {y}).Finite := by
  constructor
  · intro hker y
    by_cases hy : (f ⁻¹' {y}).Nonempty
    · obtain ⟨a, ha⟩ := hy
      change f a = y at ha
      refine Set.Finite.of_injOn (f := fun x : G => x / a) ?_ div_left_injective.injOn hker
      intro x hx
      change f x = y at hx
      exact f.div_mem_ker_iff.mpr (hx.trans ha.symm)
    · rw [Set.not_nonempty_iff_eq_empty.mp hy]
      exact Set.finite_empty
  · intro hfibers
    change (f.ker : Set G).Finite
    rw [f.coe_ker]
    exact hfibers 1

end MonoidHom
