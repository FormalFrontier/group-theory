/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.WellFoundedSet

/-!
# Finite multiplicative images in ordered types

Positive left multiplication fixes every element of a finite multiplicative image
when it is strictly increasing. With a target identity, every positive image value
is therefore one. For a nonnegative image, finiteness is equivalent to every value
being zero or one.

The Boolean criterion needs only multiplication on the source. For unital
multiplicative maps from a group with zero, a nonnegative image is finite exactly
when every value is at most one. This unit-bound criterion needs only
multiplication and a distinguished one in the target, not global identity laws
or preservation of zero. Neither criterion requires target associativity or zero
absorption.
-/

@[expose] public section

universe u v w

namespace MulHomClass

variable {M : Type u} {Γ : Type v} {F : Type w}

section Mul

variable [Mul M] [Mul Γ] [Zero Γ] [LinearOrder Γ] [PosMulStrictMono Γ]
  [FunLike F M Γ] [MulHomClass F M Γ]

/-- A positive value of a multiplicative map with finite image acts as a left
identity on its image. No nonnegativity assumption on the other values is needed. -/
theorem mul_apply_eq_right_of_pos_of_finite_range (f : F)
    (hfinite : (Set.range (f : M → Γ)).Finite) {x : M} (hx : 0 < f x) (y : M) :
    f x * f y = f y := by
  classical
  let := hfinite.fintype
  let g : Set.range (f : M → Γ) → Set.range (f : M → Γ) := fun b =>
    ⟨f x * b, by
      rcases b.property with ⟨z, hz⟩
      exact ⟨x * z, (map_mul f x z).trans (congrArg (fun c : Γ => f x * c) hz)⟩⟩
  have hg : StrictMono g := by
    intro b c hbc
    exact mul_lt_mul_of_pos_left hbc hx
  let : WellFoundedLT (Set.range (f : M → Γ)) :=
    Set.isWF_univ_iff.mp (Set.toFinite (Set.univ : Set (Set.range (f : M → Γ)))).isWF
  let : WellFoundedLT (Set.range (f : M → Γ))ᵒᵈ :=
    Set.isWF_univ_iff.mp
      (Set.toFinite (Set.univ : Set (Set.range (f : M → Γ))ᵒᵈ)).isWF
  have hgdual : StrictMono (OrderDual.toDual ∘ g ∘ OrderDual.ofDual) :=
    strictMono_dual_iff.mpr hg
  have hfix (b : Set.range (f : M → Γ)) : g b = b :=
    le_antisymm ((StrictMono.id_le hgdual) (OrderDual.toDual b))
      ((StrictMono.id_le hg) b)
  exact congrArg Subtype.val (hfix ⟨f y, ⟨y, rfl⟩⟩)

end Mul

section MulOneClass

variable [Mul M] [MulOneClass Γ] [Zero Γ] [LinearOrder Γ] [PosMulStrictMono Γ]
  [FunLike F M Γ] [MulHomClass F M Γ]

/-- A positive value of a multiplicative map with finite image is one. -/
theorem map_eq_one_of_pos_of_finite_range (f : F)
    (hfinite : (Set.range (f : M → Γ)).Finite) {x : M} (hx : 0 < f x) : f x = 1 := by
  have hstrict : StrictMono (fun b : Γ => f x * b) := by
    intro b c hbc
    exact mul_lt_mul_of_pos_left hbc hx
  exact hstrict.injective (by
    simpa only [mul_one] using
      mul_apply_eq_right_of_pos_of_finite_range f hfinite hx x)

/-- A nonnegative multiplicative image is finite exactly when all its values
are zero or one. No source identity or nontriviality assumption is required. -/
theorem finite_range_iff (f : F) (hnonneg : ∀ x : M, 0 ≤ f x) :
    (Set.range (f : M → Γ)).Finite ↔ ∀ x : M, f x = 0 ∨ f x = 1 := by
  constructor
  · intro hfinite x
    rcases eq_or_lt_of_le (hnonneg x) with hz | hx
    · exact Or.inl hz.symm
    · exact Or.inr (map_eq_one_of_pos_of_finite_range f hfinite hx)
  · intro hvalues
    refine ((Set.finite_singleton (0 : Γ)).union (Set.finite_singleton (1 : Γ))).subset ?_
    rintro _ ⟨x, rfl⟩
    simpa only [Set.mem_union, Set.mem_singleton_iff] using hvalues x

end MulOneClass

end MulHomClass

namespace MonoidHomClass

/-- A nonnegative unital multiplicative map from a group with zero has finite
range exactly when every value is at most one. The target has multiplication
and a distinguished one but need not satisfy global identity laws, and the map
need not preserve zero. -/
theorem finite_range_iff_le_one
    {M : Type u} {Γ : Type v} {F : Type w}
    [GroupWithZero M] [MulOne Γ] [Zero Γ] [LinearOrder Γ] [PosMulStrictMono Γ]
    [FunLike F M Γ] [MonoidHomClass F M Γ]
    (f : F) (hnonneg : ∀ x : M, 0 ≤ f x) :
    (Set.range (f : M → Γ)).Finite ↔ ∀ x : M, f x ≤ 1 := by
  classical
  have hright (y : M) : f y * 1 = f y := by
    calc
      f y * 1 = f y * f 1 := by rw [map_one]
      _ = f (y * 1) := (map_mul f y 1).symm
      _ = f y := congrArg f (mul_one y)
  have hzero_le_one : (0 : Γ) ≤ 1 := by
    simpa only [map_one] using hnonneg (1 : M)
  constructor
  · intro hfinite x
    rcases eq_or_lt_of_le (hnonneg x) with hz | hx
    · calc
        f x = 0 := hz.symm
        _ ≤ 1 := hzero_le_one
    · have hfix : f x * 1 = 1 := by
        simpa only [map_one] using
          (MulHomClass.mul_apply_eq_right_of_pos_of_finite_range f hfinite hx (1 : M))
      exact le_of_eq ((hright x).symm.trans hfix)
  · intro hbound
    have hvalues (x : M) : f x = 0 ∨ f x = 1 := by
      rcases eq_or_lt_of_le (hnonneg x) with hz | hx
      · exact Or.inl hz.symm
      · right
        by_cases hsource : x = 0
        · have hidem : f x * f x = f x := by
            calc
              f x * f x = f (x * x) := (map_mul f x x).symm
              _ = f x := by rw [hsource, zero_mul]
          refine le_antisymm (hbound x) ?_
          by_contra hnot
          have hlt : f x < 1 := lt_of_not_ge hnot
          have hmul : f x * f x < f x * 1 := mul_lt_mul_of_pos_left hlt hx
          rw [hidem, hright x] at hmul
          exact (lt_irrefl (f x)) hmul
        · have hinv : f x * f (x⁻¹) = 1 := by
            calc
              f x * f (x⁻¹) = f (x * x⁻¹) := (map_mul f x (x⁻¹)).symm
              _ = f 1 := congrArg f (mul_inv_cancel₀ hsource)
              _ = 1 := map_one f
          have hmul_le : f x * f (x⁻¹) ≤ f x * 1 := by
            rcases lt_or_eq_of_le (hbound (x⁻¹)) with hlt | heq
            · exact le_of_lt (mul_lt_mul_of_pos_left hlt hx)
            · exact le_of_eq (congrArg (fun b : Γ => f x * b) heq)
          refine le_antisymm (hbound x) ?_
          calc
            1 = f x * f (x⁻¹) := hinv.symm
            _ ≤ f x * 1 := hmul_le
            _ = f x := hright x
    refine (Set.Finite.insert (0 : Γ) (Set.finite_singleton (1 : Γ))).subset ?_
    rintro _ ⟨x, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hvalues x

end MonoidHomClass
