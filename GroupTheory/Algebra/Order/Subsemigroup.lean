/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Subsemigroup.MulOpposite
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bounded multiplicatively closed sets

In a multiplicatively Archimedean commutative monoid with a linear order, `0 ≤ 1`, and strictly
monotone multiplication by positive elements, a multiplicatively closed set is bounded above
if and only if each of its elements is at most `1`. The set need not contain `1`.

The same boundedness criterion holds in a conditionally complete linearly ordered group with zero,
without assuming commutativity or the multiplicative Archimedean property. Neither criterion
requires nonnegativity of the set: the forward implication uses a hypothetical element greater
than `1`.

A nonnegative multiplicatively closed set is finite if and only if both it and its inversion image
are bounded above. These two bounds force every element to be `0` or `1`, including when the set is
empty or contains zero. If the set is closed under inverses, its own boundedness suffices.

Applying this criterion to the range of a multiplicative map requires only multiplication on
its source, without an identity, associativity, or a power operation.
-/

@[expose] public section

universe u v w

namespace MulMemClass

section MulArchimedean

variable {Γ : Type u} {S : Type v}
  [CommMonoid Γ] [Zero Γ] [LinearOrder Γ] [ZeroLEOneClass Γ]
  [PosMulStrictMono Γ] [MulArchimedean Γ] [SetLike S Γ] [MulMemClass S Γ]

/-- In a multiplicatively Archimedean commutative monoid with `0 ≤ 1` and strictly monotone
multiplication by positive elements, a multiplicatively closed set is bounded above exactly when
all its elements are at most one. The set need not contain one or be nonempty. -/
theorem bddAbove_iff_le_one_of_mulArchimedean (s : S) :
    BddAbove (s : Set Γ) ↔ ∀ a ∈ s, a ≤ 1 := by
  constructor
  · rintro ⟨b, hb⟩ a ha
    by_contra ha_one
    have ha_gt : 1 < a := lt_of_not_ge ha_one
    have hb_gt : 1 < b := ha_gt.trans_le (hb ha)
    have hb_pos : 0 < b := lt_of_le_of_lt zero_le_one hb_gt
    have hb_mul : b < b * a := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left ha_gt hb_pos
    obtain ⟨n, hn⟩ := MulArchimedean.arch (b * a) ha_gt
    cases n with
    | zero =>
      have hba_one : b * a ≤ 1 := by simpa only [pow_zero] using hn
      exact (not_lt_of_ge hba_one) (hb_gt.trans hb_mul)
    | succ n =>
      have hpow : ∀ k : ℕ, a ^ (k + 1) ∈ s := by
        intro k
        induction k with
        | zero => simpa only [Nat.zero_add, pow_one] using ha
        | succ k ih =>
          rw [pow_succ]
          exact mul_mem ih ha
      exact (not_lt_of_ge (hn.trans (hb (hpow n)))) hb_mul
  · intro hs
    exact ⟨1, hs⟩

end MulArchimedean

variable {K : Type u} {S : Type v}
  [GroupWithZero K] [ConditionallyCompleteLinearOrder K] [ZeroLEOneClass K]
  [PosMulStrictMono K] [MulPosReflectLT K] [SetLike S K] [MulMemClass S K]

/-- A multiplicatively closed set is bounded above exactly when all its elements are at most one. -/
theorem bddAbove_iff_le_one (s : S) :
    BddAbove (s : Set K) ↔ ∀ x ∈ s, x ≤ 1 := by
  constructor
  · intro hs x hx
    by_contra hx_one
    have hx_gt : 1 < x := lt_of_not_ge hx_one
    have hx_pos : 0 < x := lt_of_le_of_lt zero_le_one hx_gt
    have hc_pos : 0 < sSup (s : Set K) := hx_pos.trans_le (le_csSup hs hx)
    have hbound : ∀ y ∈ s, y ≤ sSup (s : Set K) / x := by
      intro y hy
      exact (le_div_iff₀ hx_pos).2 (le_csSup hs (mul_mem hy hx))
    have hc_le : sSup (s : Set K) ≤ sSup (s : Set K) / x :=
      csSup_le ⟨x, hx⟩ hbound
    have hc_lt : sSup (s : Set K) < sSup (s : Set K) * x := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hx_gt hc_pos
    exact (not_lt_of_ge hc_le) ((div_lt_iff₀ hx_pos).2 hc_lt)
  · intro hs
    exact ⟨1, hs⟩

/-- An element of a nonnegative multiplicatively closed set is zero or one if both the set and
its inversion image are bounded above. Inverse closure is not required, and zero is allowed. -/
theorem eq_zero_or_eq_one_of_bddAbove_of_bddAbove_inv (s : S)
    (hnonneg : ∀ a ∈ s, 0 ≤ a) (hs : BddAbove (s : Set K))
    (hinv : BddAbove ((fun a : K => a⁻¹) '' (s : Set K)))
    {a : K} (ha : a ∈ s) : a = 0 ∨ a = 1 := by
  let t := ((Subsemigroup.ofClass s).op).comap (MulEquiv.inv' K).toMulHom
  have ht (x : K) : x ∈ t ↔ x⁻¹ ∈ s := Iff.rfl
  have ht_bdd : BddAbove (t : Set K) := hinv.mono (by
    intro x hx
    exact ⟨x⁻¹, (ht x).mp hx, inv_inv x⟩)
  have hle : ∀ x ∈ s, x ≤ 1 := (bddAbove_iff_le_one s).mp hs
  have ha_inv : a⁻¹ ∈ t := (ht _).mpr (by simpa only [inv_inv] using ha)
  have hle_inv : a⁻¹ ≤ 1 := (bddAbove_iff_le_one t).mp ht_bdd _ ha_inv
  rcases inv_le_one_iff₀.mp hle_inv with ha_nonpos | ha_one
  · exact Or.inl (le_antisymm ha_nonpos (hnonneg a ha))
  · exact Or.inr (le_antisymm (hle a ha) ha_one)

/-- A nonnegative multiplicatively closed set is finite exactly when both the set and its
inversion image are bounded above. No inverse closure or exclusion of zero is needed. -/
theorem finite_iff_bddAbove_and_bddAbove_inv (s : S)
    (hnonneg : ∀ a ∈ s, 0 ≤ a) :
    (s : Set K).Finite ↔ BddAbove (s : Set K) ∧
      BddAbove ((fun a : K => a⁻¹) '' (s : Set K)) := by
  constructor
  · intro hs
    exact ⟨hs.bddAbove, (hs.image fun a : K => a⁻¹).bddAbove⟩
  · rintro ⟨hs, hinv⟩
    refine (Set.Finite.insert (0 : K) (Set.finite_singleton (1 : K))).subset ?_
    intro a ha
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      eq_zero_or_eq_one_of_bddAbove_of_bddAbove_inv s hnonneg hs hinv ha

/-- Every element of a bounded-above, nonnegative, inverse-closed multiplicatively closed set
is zero or one. -/
theorem eq_zero_or_eq_one_of_bddAbove_of_inv_mem (s : S)
    (hnonneg : ∀ a ∈ s, 0 ≤ a) (hinv : ∀ a ∈ s, a⁻¹ ∈ s)
    (hs : BddAbove (s : Set K)) {a : K} (ha : a ∈ s) : a = 0 ∨ a = 1 := by
  apply eq_zero_or_eq_one_of_bddAbove_of_bddAbove_inv s hnonneg hs ?_ ha
  apply hs.mono
  rintro _ ⟨a, ha, rfl⟩
  exact hinv a ha

/-- A nonnegative, inverse-closed multiplicatively closed set is finite exactly when it is
bounded above. -/
theorem finite_iff_bddAbove_of_inv_mem (s : S)
    (hnonneg : ∀ a ∈ s, 0 ≤ a) (hinv : ∀ a ∈ s, a⁻¹ ∈ s) :
    (s : Set K).Finite ↔ BddAbove (s : Set K) := by
  constructor
  · exact Set.Finite.bddAbove
  · intro hs
    apply (finite_iff_bddAbove_and_bddAbove_inv s hnonneg).mpr
    refine ⟨hs, hs.mono ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hinv a ha

end MulMemClass

namespace MulHomClass

section MulArchimedean

variable {M : Type u} {Γ : Type v} {F : Type w}
  [Mul M] [CommMonoid Γ] [Zero Γ] [LinearOrder Γ] [ZeroLEOneClass Γ]
  [PosMulStrictMono Γ] [MulArchimedean Γ] [FunLike F M Γ] [MulHomClass F M Γ]

/-- The range of a multiplicative map into a multiplicatively Archimedean commutative monoid
with `0 ≤ 1` and strictly monotone multiplication by positive elements is bounded above exactly
when every value is at most one. Only multiplication is required on the source. -/
theorem bddAbove_range_iff_le_one_of_mulArchimedean (f : F) :
    BddAbove (Set.range f) ↔ ∀ x, f x ≤ 1 := by
  rw [← MulHom.coe_coe f, ← MulHom.coe_srange (MulHomClass.toMulHom f),
    MulMemClass.bddAbove_iff_le_one_of_mulArchimedean]
  constructor
  · intro h x
    exact h _ (MulHom.mem_srange.mpr ⟨x, rfl⟩)
  · intro h y hy
    obtain ⟨x, rfl⟩ := MulHom.mem_srange.mp hy
    exact h x

end MulArchimedean

variable {M : Type u} {K : Type v} {F : Type w}
  [Mul M] [GroupWithZero K] [ConditionallyCompleteLinearOrder K] [ZeroLEOneClass K]
  [PosMulStrictMono K] [MulPosReflectLT K] [FunLike F M K] [MulHomClass F M K]

/-- The range of a multiplicative map is bounded above exactly when every value is at most one.
Only multiplication is required on the source. -/
theorem bddAbove_range_iff_le_one (f : F) :
    BddAbove (Set.range f) ↔ ∀ x, f x ≤ 1 := by
  rw [← MulHom.coe_coe f, ← MulHom.coe_srange (MulHomClass.toMulHom f),
    MulMemClass.bddAbove_iff_le_one]
  constructor
  · intro h x
    exact h _ (MulHom.mem_srange.mpr ⟨x, rfl⟩)
  · intro h y hy
    obtain ⟨x, rfl⟩ := MulHom.mem_srange.mp hy
    exact h x

end MulHomClass
