/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Regular.Basic

/-!
# Restriction of homomorphisms through powers

If every element of a monoid has a positive power in the range of a homomorphism,
precomposition is injective for homomorphisms into a monoid with unique positive roots.
For a linearly ordered commutative monoid with zero, pointwise comparison can likewise
be checked on that range. The positive exponent may depend on the element.

If the image of a homomorphism contains a finite set of powers of every element whose
exponents have gcd one, equality after precomposition detects equality of fixed
homomorphisms whenever the values of the first homomorphism are left-regular. The finite
set may depend on the element. No regularity is required of the second map, and the
target need not be cancellative. The additive form uses natural multiples with gcd one.
Coprime pairs and consecutive powers specialize this result; consecutive powers also give
injectivity of precomposition for left-cancellative targets. Exponents and coefficients may
be zero; empty or all-zero sets cannot have gcd one.

In any monoid, if the first element is left-regular, equality at a finite family of powers
is equivalent to equality at the gcd of their exponents. When this gcd is one, the family
distinguishes the elements. Only left multiplication by the first element must be injective;
the second element is unrestricted. This combines `IsLeftRegular.pow_gcd_eq_pow_gcd_iff`
with Mathlib's `Finset.gcd` API, including empty families and zero exponents. The additive
images require only an additive monoid and injective left addition by the first element.
The `Finset` statements retain the left-cancellative specialization.

The same finite-family criterion holds when the first element is right-regular, with
no regularity assumption on the second element. A family with gcd one determines the
element; in particular, two coprime exponents suffice. The additive statements require
only an additive monoid and injective right addition by the first element.
The right-regular multiplicative and additive statements use the corresponding
left-regular kernels through Mathlib's opposite structures.

The domain of the precomposed homomorphism needs only the stock `MulOne` structure:
its associativity, identity laws and powers are not used. The intermediate monoid need
not be commutative or ordered, and none of the targets need be groups.
-/

@[expose] public section

universe u v w

section LeftRegularPowerKernels

variable {T : Type w} [Monoid T]

namespace IsLeftRegular

/-- If left multiplication by `a` is injective, the powers of `a` and `b` agree at the gcd
of two exponents if and only if they agree at both exponents. The exponents may be zero. -/
@[to_additive
  /-- If left addition by `a` is injective, the multiples of `a` and `b` agree at the gcd
  of two coefficients if and only if they agree at both coefficients. The coefficients may
  be zero. -/]
theorem pow_gcd_eq_pow_gcd_iff {a : T} (ha : IsLeftRegular a) (b : T) (m n : ℕ) :
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
          apply IsLeftRegular.pow (m * (n / m)) ha
          calc
            a ^ (m * (n / m)) * a ^ (n % m) = a ^ n := by
              rw [← pow_add, Nat.add_comm, Nat.mod_add_div]
            _ = b ^ n := hn
            _ = b ^ (m * (n / m)) * b ^ (n % m) := by
              rw [← pow_add, Nat.add_comm, Nat.mod_add_div]
            _ = a ^ (m * (n / m)) * b ^ (n % m) := by rw [hmul]
        rw [Nat.gcd_rec]
        exact ih (n % m) (Nat.mod_lt n (Nat.pos_of_ne_zero hm0)) m ⟨hrem, hm⟩

end IsLeftRegular

end LeftRegularPowerKernels

/-- If right multiplication by `a` is injective, the powers of `a` and `b` agree at the gcd
of two exponents if and only if they agree at both exponents. The exponents may be zero. -/
@[to_additive
  /-- If right addition by `a` is injective, the multiples of `a` and `b` agree at the gcd
  of two coefficients if and only if they agree at both coefficients. The coefficients may
  be zero. -/]
theorem IsRightRegular.pow_gcd_eq_pow_gcd_iff {T : Type w} [Monoid T] {a : T}
    (ha : IsRightRegular a) (b : T) (m n : ℕ) :
    a ^ Nat.gcd m n = b ^ Nat.gcd m n ↔ a ^ m = b ^ m ∧ a ^ n = b ^ n := by
  have haop : IsLeftRegular (MulOpposite.op a) := by
    intro x y h
    exact congrArg MulOpposite.op (ha (congrArg MulOpposite.unop h))
  have hop (x y : T) : MulOpposite.op x = MulOpposite.op y ↔ x = y :=
    ⟨fun h => congrArg MulOpposite.unop h, fun h => congrArg MulOpposite.op h⟩
  simpa only [← MulOpposite.op_pow, hop] using
    (IsLeftRegular.pow_gcd_eq_pow_gcd_iff haop (MulOpposite.op b) m n)

/-- Agreement at two coprime powers determines an element whose right multiplication
is injective. -/
@[to_additive
  /-- Agreement at two coprime multiples determines an element whose right addition
  is injective. -/]
theorem IsRightRegular.eq_of_pow_eq_pow_of_coprime {T : Type w} [Monoid T]
    {a b : T} {m n : ℕ} (ha : IsRightRegular a) (hcop : Nat.Coprime m n)
    (hm : a ^ m = b ^ m) (hn : a ^ n = b ^ n) : a = b := by
  have hgcd := (ha.pow_gcd_eq_pow_gcd_iff b m n).2 ⟨hm, hn⟩
  simpa only [hcop.gcd_eq_one, pow_one] using hgcd

section PowerKernels

variable {T : Type w} [LeftCancelMonoid T]

/-- Two elements of a left-cancellative monoid have equal powers at the gcd of two
exponents if and only if they have equal powers at both exponents. -/
@[to_additive
  /-- Two elements of a left-cancellative additive monoid have equal multiples at the gcd
  of two coefficients if and only if they have equal multiples at both coefficients. -/]
theorem pow_gcd_eq_pow_gcd_iff (a b : T) (m n : ℕ) :
    a ^ Nat.gcd m n = b ^ Nat.gcd m n ↔ a ^ m = b ^ m ∧ a ^ n = b ^ n := by
  exact IsLeftRegular.pow_gcd_eq_pow_gcd_iff (a := a)
    (fun _ _ h => mul_left_cancel h) b m n

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


end MonoidHom

namespace IsLeftRegular

variable {ι : Type u} {T : Type v} [Monoid T]

/-- If left multiplication by `a` is injective, the powers of `a` and any `b` agree at
the gcd of a finite family of exponents if and only if they agree at every selected
exponent. Empty families and zero exponents are included. -/
@[to_additive
  /-- If left addition by `a` is injective, the multiples of `a` and any `b` agree at
  the gcd of a finite family of coefficients if and only if they agree at every selected
  coefficient. Empty families and zero coefficients are included. -/]
theorem pow_finset_gcd_eq_pow_finset_gcd_iff {a : T} (ha : IsLeftRegular a)
    (b : T) (s : Finset ι) (e : ι → ℕ) :
    a ^ (s.gcd e) = b ^ (s.gcd e) ↔ ∀ i ∈ s, a ^ (e i) = b ^ (e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ ih =>
      rw [Finset.gcd_insert, gcd_eq_nat_gcd, ha.pow_gcd_eq_pow_gcd_iff, ih,
        Finset.forall_mem_insert]

/-- A finite family of powers with gcd one distinguishes a left-regular element
from any other element of a monoid. -/
@[to_additive eq_of_forall_nsmul_eq_of_gcd_eq_one
  /-- A finite family of natural multiples with gcd one distinguishes an add-left-regular
  element from any other element of an additive monoid. -/]
theorem eq_of_forall_pow_eq_of_gcd_eq_one {a : T} (ha : IsLeftRegular a)
    {s : Finset ι} {e : ι → ℕ} {b : T}
    (hg : s.gcd e = 1) (h : ∀ i ∈ s, a ^ (e i) = b ^ (e i)) : a = b := by
  have hab := (ha.pow_finset_gcd_eq_pow_finset_gcd_iff b s e).2 h
  simpa only [hg, pow_one] using hab

end IsLeftRegular

namespace IsRightRegular

variable {ι : Type u} {T : Type v} [Monoid T]

/-- If right multiplication by `a` is injective, the powers of `a` and any `b` agree at
the gcd of a finite family of exponents if and only if they agree at every selected
exponent. Empty families and zero exponents are included. -/
@[to_additive
  /-- If right addition by `a` is injective, the multiples of `a` and any `b` agree at
  the gcd of a finite family of coefficients if and only if they agree at every selected
  coefficient. Empty families and zero coefficients are included. -/]
theorem pow_finset_gcd_eq_pow_finset_gcd_iff {a : T} (ha : IsRightRegular a)
    (b : T) (s : Finset ι) (e : ι → ℕ) :
    a ^ (s.gcd e) = b ^ (s.gcd e) ↔ ∀ i ∈ s, a ^ (e i) = b ^ (e i) := by
  have haop : IsLeftRegular (MulOpposite.op a) := by
    intro x y h
    exact congrArg MulOpposite.op (ha (congrArg MulOpposite.unop h))
  have hop (x y : T) : MulOpposite.op x = MulOpposite.op y ↔ x = y :=
    ⟨fun h => congrArg MulOpposite.unop h, fun h => congrArg MulOpposite.op h⟩
  simpa only [← MulOpposite.op_pow, hop] using
    (IsLeftRegular.pow_finset_gcd_eq_pow_finset_gcd_iff haop (MulOpposite.op b) s e)

/-- A finite family of powers with gcd one distinguishes a right-regular element
from any other element of a monoid. -/
@[to_additive eq_of_forall_nsmul_eq_of_gcd_eq_one
  /-- A finite family of natural multiples with gcd one distinguishes an add-right-regular
  element from any other element of an additive monoid. -/]
theorem eq_of_forall_pow_eq_of_gcd_eq_one {a : T} (ha : IsRightRegular a)
    {s : Finset ι} {e : ι → ℕ} {b : T}
    (hg : s.gcd e = 1) (h : ∀ i ∈ s, a ^ (e i) = b ^ (e i)) : a = b := by
  have hab := (ha.pow_finset_gcd_eq_pow_finset_gcd_iff b s e).2 h
  simpa only [hg, pow_one] using hab

end IsRightRegular

namespace Finset

variable {ι : Type u} {T : Type v} [LeftCancelMonoid T]

/-- Two elements of a left-cancellative monoid have equal powers at the gcd of a finite
family of exponents if and only if they have equal powers at every exponent in the family. -/
theorem pow_gcd_eq_pow_gcd_iff (s : Finset ι) (e : ι → ℕ) (a b : T) :
    a ^ (s.gcd e) = b ^ (s.gcd e) ↔ ∀ i ∈ s, a ^ (e i) = b ^ (e i) :=
  (IsLeftRegular.all a).pow_finset_gcd_eq_pow_finset_gcd_iff b s e

/-- A finite family of powers whose exponents have gcd one distinguishes elements of a
left-cancellative monoid. -/
theorem eq_of_forall_pow_eq_of_gcd_eq_one {s : Finset ι} {e : ι → ℕ} {a b : T}
    (hg : s.gcd e = 1) (h : ∀ i ∈ s, a ^ (e i) = b ^ (e i)) : a = b :=
  (IsLeftRegular.all a).eq_of_forall_pow_eq_of_gcd_eq_one hg h

end Finset

namespace MonoidHom

section RegularValues

universe uA uM uN uι

/-- Equality of homomorphisms can be tested on an image containing a finite indexed
family of powers of every element with gcd one, provided the values of the first
homomorphism are left-regular. The finite index set and exponent function may both
depend on the element; exponents may be zero or repeated. -/
@[to_additive
  /-- Equality of additive homomorphisms can be tested on an image containing a finite
  indexed family of natural multiples of every element with gcd one, provided the values
  of the first homomorphism are add-left-regular. The finite index set and coefficient
  function may both depend on the element; coefficients may be zero or repeated. -/]
theorem cancel_right_of_finite_powers_mem_range_of_isLeftRegular
    {A : Type uA} {M : Type uM} {N : Type uN} {ι : Type uι}
    [MulOne A] [Monoid M] [Monoid N]
    (f : A →* M)
    (hfamily : ∀ x : M, ∃ s : Finset ι, ∃ e : ι → ℕ,
      s.gcd e = 1 ∧ ∀ i ∈ s, x ^ (e i) ∈ Set.range f)
    (g h : M →* N) (hg : ∀ x : M, IsLeftRegular (g x)) :
    g.comp f = h.comp f ↔ g = h := by
  constructor
  · intro hcomp
    apply MonoidHom.ext
    intro x
    obtain ⟨s, e, hgcd, hs⟩ := hfamily x
    apply IsLeftRegular.eq_of_forall_pow_eq_of_gcd_eq_one (hg x) (e := e) hgcd
    intro i hi
    obtain ⟨a, ha⟩ := hs i hi
    calc
      g x ^ (e i) = g (x ^ (e i)) := (g.map_pow x (e i)).symm
      _ = g (f a) := congrArg g ha.symm
      _ = h (f a) := by
        simpa only [MonoidHom.comp_apply] using
          congrArg (fun q : A →* N => q a) hcomp
      _ = h (x ^ (e i)) := congrArg h ha
      _ = h x ^ (e i) := h.map_pow x (e i)
  · intro hgh
    exact congrArg (fun q : M →* N => q.comp f) hgh

/-- Equality of homomorphisms can be tested on an image containing a finite set of
powers of every element with gcd one, provided the values of the first homomorphism
are left-regular. The finite set may depend on the element, and exponents may be zero. -/
@[to_additive
  /-- Equality of additive homomorphisms can be tested on an image containing a finite set
  of natural multiples of every element with gcd one, provided the values of the first
  homomorphism are add-left-regular. The finite set may depend on the element, and
  coefficients may be zero. -/]
theorem cancel_right_of_finite_powers_mem_range
    {A : Type u} {M : Type v} {N : Type w}
    [MulOne A] [Monoid M] [Monoid N]
    (h : A →* M)
    (hpowers : ∀ x : M, ∃ s : Finset ℕ,
      s.gcd _root_.id = 1 ∧ ∀ n ∈ s, x ^ n ∈ Set.range h)
    (f g : M →* N) (hf : ∀ x : M, IsLeftRegular (f x)) :
    f.comp h = g.comp h ↔ f = g := by
  apply cancel_right_of_finite_powers_mem_range_of_isLeftRegular
    (ι := ℕ) h ?_ f g hf
  intro x
  obtain ⟨s, hg, hs⟩ := hpowers x
  exact ⟨s, _root_.id, hg, hs⟩

/-- Equality of homomorphisms can be tested on an image containing two coprime
powers of every element, provided the values of the first homomorphism are
left-regular. The exponents may be zero. -/
@[to_additive
  /-- Equality of additive homomorphisms can be tested on an image containing two
  coprime multiples of every element, provided the values of the first
  homomorphism are add-left-regular. The coefficients may be zero. -/]
theorem cancel_right_of_coprime_powers_mem_range
    {A : Type u} {M : Type v} {N : Type w}
    [MulOne A] [Monoid M] [Monoid N]
    (h : A →* M)
    (hpowers : ∀ x : M, ∃ m n : ℕ,
      Nat.Coprime m n ∧ x ^ m ∈ Set.range h ∧ x ^ n ∈ Set.range h)
    (f g : M →* N) (hf : ∀ x : M, IsLeftRegular (f x)) :
    f.comp h = g.comp h ↔ f = g := by
  apply cancel_right_of_finite_powers_mem_range h (hpowers := ?_) f g hf
  intro x
  obtain ⟨m, n, hmn, hm, hn⟩ := hpowers x
  refine ⟨{m, n}, ?_, ?_⟩
  · simpa [gcd_eq_nat_gcd] using hmn.gcd_eq_one
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hm
    · exact hn

/-- Equality of two monoid homomorphisms can be checked after precomposition with a
homomorphism whose range contains two successive powers of every element, provided that
every value of the first homomorphism is left-regular. The exponent may be zero. -/
theorem cancel_right_of_successive_powers_mem_range
    {A : Type u} {M : Type v} {N : Type w}
    [MulOne A] [Monoid M] [Monoid N]
    (h : A →* M)
    (hpowers : ∀ x : M, ∃ n : ℕ,
      x ^ n ∈ Set.range h ∧ x ^ (n + 1) ∈ Set.range h)
    (f g : M →* N) (hf : ∀ x : M, IsLeftRegular (f x)) :
    f.comp h = g.comp h ↔ f = g := by
  apply cancel_right_of_coprime_powers_mem_range h ?_ f g hf
  intro x
  obtain ⟨n, hn, hn'⟩ := hpowers x
  refine ⟨n, n + 1, ?_, hn, hn'⟩
  exact Nat.coprime_iff_gcd_eq_one.mpr (by
    simp only [Nat.gcd_self_add_right, Nat.gcd_one_right])

end RegularValues

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
  exact (cancel_right_of_successive_powers_mem_range f h g₁ g₂
    (fun x => IsLeftRegular.all (g₁ x))).mp hcomp

end SuccessivePowers

end MonoidHom

namespace MonoidHom

section RightRegularValues

universe uA uM uN uι

/-- Equality of fixed homomorphisms can be tested on an image containing a finite indexed
family of powers of each element with gcd one, provided the values of the first map are
right-regular. Both the finite set and the exponent function may depend on the element. -/
@[to_additive
  /-- Equality of fixed additive homomorphisms can be tested on an image containing a finite
  indexed family of natural multiples of each element with gcd one, provided the values of
  the first map are add-right-regular. Both the finite set and the coefficient function may
  depend on the element. -/]
theorem cancel_right_of_finite_powers_mem_range_of_isRightRegular
    {A : Type uA} {M : Type uM} {N : Type uN} {ι : Type uι}
    [MulOne A] [Monoid M] [Monoid N]
    (f : A →* M)
    (hfamily : ∀ x : M, ∃ s : Finset ι, ∃ e : ι → ℕ,
      s.gcd e = 1 ∧ ∀ i ∈ s, x ^ (e i) ∈ Set.range f)
    (g h : M →* N) (hg : ∀ x : M, IsRightRegular (g x)) :
    g.comp f = h.comp f ↔ g = h := by
  constructor
  · intro hcomp
    apply MonoidHom.ext
    intro x
    obtain ⟨s, e, hgcd, hs⟩ := hfamily x
    apply IsRightRegular.eq_of_forall_pow_eq_of_gcd_eq_one (hg x) hgcd
    intro i hi
    obtain ⟨a, ha⟩ := hs i hi
    calc
      (g x) ^ (e i) = g (x ^ (e i)) := (g.map_pow x (e i)).symm
      _ = h (x ^ (e i)) := by
        simpa only [MonoidHom.comp_apply, ha] using
          congrArg (fun k : A →* N => k a) hcomp
      _ = (h x) ^ (e i) := h.map_pow x (e i)
  · rintro rfl
    rfl

end RightRegularValues

end MonoidHom
