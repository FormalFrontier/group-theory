/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Restriction of homomorphisms through powers

If every element of a monoid has a positive power in the range of a homomorphism,
precomposition is injective for homomorphisms into a monoid with unique positive roots.
For a linearly ordered commutative monoid with zero, pointwise comparison can likewise
be checked on that range. The positive exponent may depend on the element.

If two consecutive powers of every element lie in the range, precomposition is injective
for homomorphisms into any left-cancellative monoid. Here the exponent may be zero.

The domain of the precomposed homomorphism needs only the stock `MulOne` structure:
its associativity, identity laws and powers are not used. The intermediate monoid need
not be commutative or ordered, and none of the targets need be groups.
-/

@[expose] public section

universe u v w

section PowerKernels

variable {T : Type w} [LeftCancelMonoid T]

/-- Two elements of a left-cancellative monoid have equal powers at the gcd of two
exponents if and only if they have equal powers at both exponents. -/
@[to_additive
  /-- Two elements of a left-cancellative additive monoid have equal multiples at the gcd
  of two coefficients if and only if they have equal multiples at both coefficients. -/]
theorem pow_gcd_eq_pow_gcd_iff (a b : T) (m n : ℕ) :
    a ^ Nat.gcd m n = b ^ Nat.gcd m n ↔ a ^ m = b ^ m ∧ a ^ n = b ^ n := by
  constructor
  · intro h
    constructor
    · obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m n
      simpa only [← pow_mul, ← hk] using congrArg (fun x : T => x ^ k) h
    · obtain ⟨k, hk⟩ := Nat.gcd_dvd_right m n
      simpa only [← pow_mul, ← hk] using congrArg (fun x : T => x ^ k) h
  · revert n
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rintro n ⟨hm, hn⟩
      by_cases hm0 : m = 0
      · simpa only [hm0, Nat.gcd_zero_left] using hn
      · have hmul : a ^ (m * (n / m)) = b ^ (m * (n / m)) := by
          simpa only [pow_mul] using congrArg (fun x : T => x ^ (n / m)) hm
        have hrem : a ^ (n % m) = b ^ (n % m) := by
          apply mul_left_cancel (a := a ^ (m * (n / m)))
          calc
            a ^ (m * (n / m)) * a ^ (n % m) = a ^ n := by
              rw [← pow_add, Nat.add_comm, Nat.mod_add_div]
            _ = b ^ n := hn
            _ = b ^ (m * (n / m)) * b ^ (n % m) := by
              rw [← pow_add, Nat.add_comm, Nat.mod_add_div]
            _ = a ^ (m * (n / m)) * b ^ (n % m) := by rw [hmul]
        rw [Nat.gcd_rec]
        exact ih (n % m) (Nat.mod_lt n (Nat.pos_of_ne_zero hm0)) m ⟨hrem, hm⟩

/-- Powers at two coprime exponents jointly distinguish elements of a left-cancellative
monoid. -/
@[to_additive
  /-- Multiples at two coprime coefficients jointly distinguish elements of a
  left-cancellative additive monoid. -/]
theorem Nat.Coprime.pow_pair_injective {m n : ℕ} (h : Nat.Coprime m n) :
    Function.Injective (fun x : T => (x ^ m, x ^ n)) := by
  intro a b hab
  have hgcd := (pow_gcd_eq_pow_gcd_iff a b m n).mpr
    ⟨congrArg Prod.fst hab, congrArg Prod.snd hab⟩
  simpa only [h.gcd_eq_one, pow_one] using hgcd

end PowerKernels

namespace MonoidHom

variable {M : Type u} {N : Type v} [MulOne M] [Monoid N]

section UniqueRoots

variable {T : Type w} [Monoid T] [IsMulTorsionFree T]

/-- Restriction along a homomorphism whose range contains a positive power of every
 element is injective on homomorphisms to a monoid with unique positive roots. -/
@[to_additive
  /-- Restriction along a homomorphism whose range contains a positive multiple of every
  element is injective on homomorphisms to a torsion-free additive monoid. -/]
theorem comp_right_injective_of_forall_pow_mem_range (f : M →* N)
    (hf : ∀ x : N, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) :
    Function.Injective (fun g : N →* T => g.comp f) := by
  intro g h heq
  apply MonoidHom.ext
  intro x
  obtain ⟨n, hn, a, ha⟩ := hf x
  have hfa : g (f a) = h (f a) := congrArg (fun k : M →* T => k a) heq
  have hpow : g x ^ n = h x ^ n := by
    simpa only [ha, map_pow] using hfa
  exact pow_left_injective (Nat.ne_of_gt hn) hpow

/-- Equality of homomorphisms into a monoid with unique positive roots can be tested
 after restriction to a range containing a positive power of every element. -/
@[to_additive
  /-- Equality of homomorphisms into a torsion-free additive monoid can be tested after
  restriction to a range containing a positive multiple of every element. -/]
theorem cancel_right_of_forall_pow_mem_range (f : M →* N)
    (hf : ∀ x : N, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f) {g h : N →* T} :
    g.comp f = h.comp f ↔ g = h :=
  (comp_right_injective_of_forall_pow_mem_range (T := T) f hf).eq_iff

end UniqueRoots

section Ordered

variable {Γ : Type w} [LinearOrderedCommMonoidWithZero Γ]

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

end Ordered

section SuccessivePowers

universe uM uN uT

/-- Precomposition is injective for homomorphisms to a left-cancellative monoid if every
element has two consecutive powers in the range. The exponent may be zero, and the domain
of the precomposed homomorphism needs only multiplication and a distinguished one. -/
theorem comp_injective_of_successive_powers_mem_range
    {M : Type uM} {N : Type uN} {T : Type uT}
    [MulOne M] [Monoid N] [LeftCancelMonoid T]
    (f : M →* N)
    (h : ∀ x : N, ∃ n : ℕ,
      x ^ n ∈ Set.range f ∧ x ^ (n + 1) ∈ Set.range f) :
    Function.Injective (fun g : N →* T => g.comp f) := by
  intro g₁ g₂ hcomp
  apply MonoidHom.ext
  intro x
  obtain ⟨n, hn, hn'⟩ := h x
  have hpow (k : ℕ) (hk : x ^ k ∈ Set.range f) : g₁ x ^ k = g₂ x ^ k := by
    obtain ⟨a, ha⟩ := hk
    calc
      g₁ x ^ k = g₁ (x ^ k) := (g₁.map_pow x k).symm
      _ = g₁ (f a) := congrArg g₁ ha.symm
      _ = g₂ (f a) := by
        simpa only [MonoidHom.comp_apply] using
          congrArg (fun q : M →* T => q a) hcomp
      _ = g₂ (x ^ k) := congrArg g₂ ha
      _ = g₂ x ^ k := g₂.map_pow x k
  have hnext := hpow (n + 1) hn'
  rw [pow_succ, pow_succ, hpow n hn] at hnext
  exact mul_left_cancel hnext

end SuccessivePowers

end MonoidHom
