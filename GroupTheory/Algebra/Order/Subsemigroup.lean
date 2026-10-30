/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bounded multiplicatively closed sets

A multiplicatively closed set in a conditionally complete linearly ordered group with zero is
bounded above if and only if each of its elements is at most `1`. No nonnegativity assumption
on the set is needed: the forward implication uses only a hypothetical element greater than `1`.

Applying this criterion to the range of a multiplicative map requires only multiplication on
its source, without an identity, associativity, or a power operation.
-/

@[expose] public section

universe u v w

namespace MulMemClass

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

end MulMemClass

namespace MulHomClass

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
