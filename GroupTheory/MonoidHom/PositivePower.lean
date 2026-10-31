/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Pointwise comparison through positive powers

If every element of a monoid has a positive power in the range of a monoid
homomorphism, pointwise comparison of homomorphisms to a linearly ordered
commutative monoid with zero can be checked on that range.

The source monoids need not be commutative or ordered. The target need not be a
group, and the positive exponent may depend on the element.
-/

@[expose] public section

namespace MonoidHom

variable {M N Γ : Type*} [Monoid M] [Monoid N]
  [LinearOrderedCommMonoidWithZero Γ]

/-- Pointwise comparison of monoid homomorphisms is reflected by restriction along
a homomorphism whose range contains a positive power of every element. -/
theorem forall_comp_le_iff_of_forall_pow_mem_range (f : M →* N)
    (hf : ∀ x : N, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) (g h : N →* Γ) :
    (∀ a : M, g (f a) ≤ h (f a)) ↔ ∀ x : N, g x ≤ h x := by
  constructor
  · intro hle x
    obtain ⟨n, hn, a, ha⟩ := hf x
    have hpow : g x ^ n ≤ h x ^ n := by
      simpa only [ha, map_pow] using hle a
    exact (pow_le_pow_iff_left₀ (zero_le : 0 ≤ g x) (zero_le : 0 ≤ h x)
      (Nat.ne_of_gt hn)).mp hpow
  · intro hle a
    exact hle (f a)

end MonoidHom
