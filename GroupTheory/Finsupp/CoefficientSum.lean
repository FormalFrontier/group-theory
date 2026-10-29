/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Relations for the coefficient sum

For a pointed index type, the kernel of the coefficient sum is spanned by
`single i m - single i₀ m`. A linear map factors uniquely through the sum exactly
when its singleton components agree. The target need only be an additive
commutative monoid; cancellation is not required. The componentwise
characterization of factorization also holds for additive commutative monoid
coefficients. Additive inverses are used for the singleton differences and the
kernel characterization.

The coefficient sum is the existing `Finsupp.lsum ℕ` of identity maps. The auxiliary
scalar is `ℕ`, even when the resulting map is linear over a noncommutative semiring.
No module structure on the space of linear maps is needed.

## References

The proofs use Mathlib's finitely supported sums and linear singleton maps.
-/

public section

namespace Finsupp

universe uR uι uM uN

variable {R : Type uR} [Semiring R] {ι : Type uι}
  {M : Type uM}

section AddCommMonoid

variable [AddCommMonoid M] [Module R M]
  {N : Type uN} [AddCommMonoid N] [Module R N]

local notation "σ" => (lsum ℕ (fun _ : ι => (LinearMap.id : M →ₗ[R] M)))

/-- The factor through the coefficient sum is obtained by composing with the
distinguished singleton map. -/
theorem comp_lsingle_comp_lsum_id (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N)
    (h : ∀ i m, T (single i m) = T (single i₀ m)) :
    (T.comp (lsingle i₀)).comp σ = T := by
  classical
  apply LinearMap.ext
  intro f
  have hs : (∑ i ∈ f.support, single i (f i)) = f := sum_single f
  calc
    ((T.comp (lsingle i₀)).comp σ) f =
        (T.comp (lsingle i₀)) (∑ i ∈ f.support, f i) := rfl
    _ = ∑ i ∈ f.support, T (single i₀ (f i)) := map_sum _ _ _
    _ = ∑ i ∈ f.support, T (single i (f i)) :=
      Finset.sum_congr rfl fun i _ => (h i (f i)).symm
    _ = T f := by rw [← map_sum, hs]

/-- The value of a map whose singleton components agree is computed from the
coefficient sum. -/
theorem apply_eq_single_lsum_id (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N)
    (h : ∀ i m, T (single i m) = T (single i₀ m)) (f : ι →₀ M) :
    T f = T (single i₀ (σ f)) := by
  exact (congrArg (fun U : (ι →₀ M) →ₗ[R] N => U f)
    (comp_lsingle_comp_lsum_id i₀ T h)).symm

/-- Every factor through the coefficient sum equals composition with the
specified singleton section. -/
theorem eq_comp_lsingle_of_comp_lsum_id_eq (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N)
    (t : M →ₗ[R] N) (h : t.comp σ = T) : t = T.comp (lsingle i₀) := by
  apply LinearMap.ext
  intro m
  have hv := congrArg (fun U : (ι →₀ M) →ₗ[R] N => U (single i₀ m)) h
  change t (σ (single i₀ m)) = T (single i₀ m) at hv
  simpa using hv

/-- A map factors uniquely through the coefficient sum if and only if all its
singleton components agree. The target needs no cancellation law. -/
theorem existsUnique_comp_lsum_id_iff (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N) :
    (∃! t : M →ₗ[R] N, t.comp σ = T) ↔
      ∀ i m, T (single i m) = T (single i₀ m) := by
  constructor
  · rintro ⟨t, ht, _⟩ i m
    have hv (j : ι) : T (single j m) = t m := by
      have he := congrArg (fun U : (ι →₀ M) →ₗ[R] N => U (single j m)) ht
      simpa using he.symm
    exact (hv i).trans (hv i₀).symm
  · intro h
    exact ⟨T.comp (lsingle i₀), comp_lsingle_comp_lsum_id i₀ T h,
      fun t ht => eq_comp_lsingle_of_comp_lsum_id_eq i₀ T t ht⟩

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module R M]

local notation "σ" => (lsum ℕ (fun _ : ι => (LinearMap.id : M →ₗ[R] M)))

/-- The sum of the singleton differences is the difference from the section of
the coefficient sum. -/
theorem sum_sub_single_eq_sub_single_lsum (i₀ : ι) (f : ι →₀ M) :
    (∑ i ∈ f.support, (single i (f i) - single i₀ (f i))) =
      f - single i₀ (σ f) := by
  classical
  rw [Finset.sum_sub_distrib]
  have hs : (∑ i ∈ f.support, single i (f i)) = f := sum_single f
  rw [hs]
  congr 1
  change (∑ i ∈ f.support, (lsingle i₀ : M →ₗ[R] (ι →₀ M)) (f i)) = _
  rw [← map_sum]
  rfl

/-- The kernel of the coefficient sum is spanned by differences of singletons
with the distinguished singleton. This holds over an arbitrary semiring. -/
theorem ker_lsum_id (i₀ : ι) :
    LinearMap.ker σ = Submodule.span R
      (Set.range fun p : ι × M => single p.1 p.2 - single i₀ p.2) := by
  apply le_antisymm
  · intro f hf
    have hz : σ f = 0 := hf
    have he : (∑ i ∈ f.support, (single i (f i) - single i₀ (f i))) = f := by
      rw [sum_sub_single_eq_sub_single_lsum (R := R), hz, single_zero, sub_zero]
    rw [← he]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨(i, f i), rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨i, m⟩, rfl⟩
    change σ (single i m - single i₀ m) = 0
    rw [map_sub]
    simp

variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- Additivity detects equality by source differences, without cancellation in
the target. -/
private theorem map_sub_eq_zero_iff_eq (T : (ι →₀ M) →ₗ[R] N) (x y : ι →₀ M) :
    T (x - y) = 0 ↔ T x = T y := by
  constructor
  · intro h
    calc
      T x = T ((x - y) + y) := congrArg T (sub_add_cancel x y).symm
      _ = T (x - y) + T y := map_add T _ _
      _ = T y := by rw [h, zero_add]
  · intro h
    calc
      T (x - y) = T x + T (-y) := by rw [sub_eq_add_neg, map_add]
      _ = T y + T (-y) := by rw [h]
      _ = T (y + -y) := (map_add T _ _).symm
      _ = 0 := by simp only [add_neg_cancel, map_zero]

/-- Annihilating singleton differences is equivalent to equality of components,
even for a target without cancellation. -/
theorem map_sub_single_eq_zero_iff (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N) :
    (∀ i m, T (single i m - single i₀ m) = 0) ↔
      ∀ i m, T (single i m) = T (single i₀ m) := by
  simp only [map_sub_eq_zero_iff_eq]

/-- Vanishing on the coefficient-sum kernel is equivalent to annihilating its
singleton-difference generators. -/
theorem ker_lsum_id_le_ker_iff (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N) :
    LinearMap.ker σ ≤ LinearMap.ker T ↔
      ∀ i m, T (single i m - single i₀ m) = 0 := by
  rw [ker_lsum_id i₀, Submodule.span_le]
  constructor
  · intro h i m
    exact h ⟨(i, m), rfl⟩
  · intro h x hx
    rcases hx with ⟨⟨i, m⟩, rfl⟩
    exact h i m

/-- The universal property of the coefficient sum is equivalently vanishing on
its kernel. -/
theorem existsUnique_comp_lsum_id_iff_vanish (i₀ : ι) (T : (ι →₀ M) →ₗ[R] N) :
    (∃! t : M →ₗ[R] N, t.comp σ = T) ↔
      ∀ f, σ f = 0 → T f = 0 := by
  rw [existsUnique_comp_lsum_id_iff i₀ T,
    ← map_sub_single_eq_zero_iff i₀ T, ← ker_lsum_id_le_ker_iff i₀ T]
  rfl

end AddCommGroup

end Finsupp
