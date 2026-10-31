/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.Order.MulHom
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Iterate

/-!
# Finite multiplicative images in ordered rings

Every value in a finite multiplicative image is zero, one, or negative one.
The source needs only multiplication.
-/

@[expose] public section

universe u v w

namespace MulHomClass

variable {M : Type u} {R : Type v} {F : Type w}
  [Mul M] [NonAssocRing R] [LinearOrder R] [IsOrderedAddMonoid R]
  [PosMulStrictMono R] [FunLike F M R] [MulHomClass F M R]

/-- Every value of a multiplicative map with finite image is zero, one, or negative one. -/
theorem map_eq_zero_or_one_or_neg_one_of_finite_range
    (f : F) (hfinite : (Set.range (f : M → R)).Finite) (x : M) :
    f x = 0 ∨ f x = 1 ∨ f x = -1 := by
  rcases lt_trichotomy (f x) 0 with hx | hx | hx
  · have hpos : 0 < -f x := neg_pos.mpr hx
    have hsquare : 0 < f (x * x) := by
      rw [map_mul, ← neg_mul_neg (f x) (f x)]
      exact mul_pos hpos hpos
    have hsquare_one : f x * f x = 1 := by
      rw [← map_mul]
      exact map_eq_one_of_pos_of_finite_range f hfinite hsquare
    have hmono : StrictMono (fun y : R => -f x * y) :=
      fun _ _ hab => mul_lt_mul_of_pos_left hab hpos
    have hcomm : Function.Commute (fun y : R => -f x * y) id := fun _ => rfl
    have htwo : (fun y : R => -f x * y)^[2] (1 : R) = id^[2] 1 := by
      change -f x * (-f x * 1) = 1
      simpa only [mul_one, neg_mul_neg] using hsquare_one
    have hone : -f x = 1 := by
      have hfixed :=
        (hcomm.iterate_pos_eq_iff_map_eq hmono.monotone (fun _ _ h => h)
          (by decide : 0 < 2)).mp htwo
      simpa only [mul_one, id_eq] using hfixed
    exact Or.inr (Or.inr (neg_eq_iff_eq_neg.mp hone))
  · exact Or.inl hx
  · exact Or.inr (Or.inl (map_eq_one_of_pos_of_finite_range f hfinite hx))

/-- A multiplicative map has finite image exactly when every value is
zero, one, or negative one. -/
theorem finite_range_iff_eq_zero_or_one_or_neg_one (f : F) :
    (Set.range (f : M → R)).Finite ↔
      ∀ x : M, f x = 0 ∨ f x = 1 ∨ f x = -1 := by
  constructor
  · intro hfinite x
    exact map_eq_zero_or_one_or_neg_one_of_finite_range f hfinite x
  · intro hvalues
    refine ((Set.finite_singleton (0 : R)).union
      ((Set.finite_singleton (1 : R)).union (Set.finite_singleton (-1 : R)))).subset ?_
    rintro _ ⟨x, rfl⟩
    simpa only [Set.mem_union, Set.mem_singleton_iff] using hvalues x

end MulHomClass
