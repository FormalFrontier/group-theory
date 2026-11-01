/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Fixed vectors of permutation representations

For a pretransitive group action on `X`, the fixed vectors in the permutation
representation `Representation.ofMulAction R G X` are precisely the vectors whose
coefficients are all equal. When `X` is finite and nonempty, these vectors form a
module linearly equivalent to `R`: the forward map gives every coefficient the
same value, and the inverse evaluates at any point of `X`.

Finite coefficient support also shows that any nonzero fixed vector forces `X` to
be finite. Thus the fixed submodule is bottom when `X` is infinite.

The coefficients may form any semiring, including a zero or noncommutative
semiring. The finite-carrier equivalence does not require the acting group to be
finite, nor does it require an invertible group order.

## References

The construction uses Mathlib's permutation representations, coefficient API,
finite sums and singleton linear maps, together with this library's fixed
submodules of semiring representations.
-/

@[expose] public section

universe uR uG uX

open MonoidAlgebra
open scoped BigOperators

namespace Representation

section MulAction

variable {R : Type uR} {G : Type uG} {X : Type uX}
variable [Semiring R] [Group G] [MulAction G X] [MulAction.IsPretransitive G X]

/-- A vector of a pretransitive permutation representation is fixed if and only if all its
coefficients agree. -/
theorem mem_fixedSubmodule_ofMulAction_iff (v : R[X]) :
    v ∈ (ofMulAction R G X).fixedSubmodule ↔ ∀ a b : X, v.coeff a = v.coeff b := by
  rw [mem_fixedSubmodule]
  constructor
  · intro hv a b
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
    simpa [← hg] using congrArg (fun w : R[X] => w.coeff b) (hv g)
  · intro hv g
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro a
    rw [coeff_ofMulAction]
    exact hv (g⁻¹ • a) a

/-- A nonzero fixed vector of a pretransitive permutation representation forces the carrier
to be finite. -/
theorem finite_of_mem_fixedSubmodule_ofMulAction_ne_zero (v : R[X])
    (hv : v ∈ (ofMulAction R G X).fixedSubmodule) (hv0 : v ≠ 0) : Finite X := by
  have hcoeff : (v.coeff : X →₀ R) ≠ 0 := by
    intro h
    apply hv0
    apply MonoidAlgebra.coeff_injective
    simpa using h
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  have ha0 : v.coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
  have hconst :=
    (mem_fixedSubmodule_ofMulAction_iff (R := R) (G := G) (X := X) v).1 hv
  apply Set.finite_univ_iff.mp
  refine (Finset.finite_toSet v.coeff.support).subset ?_
  intro b _
  apply Finsupp.mem_support_iff.mpr
  rw [hconst b a]
  exact ha0

variable (R G X)

/-- On an infinite pretransitive carrier, the permutation representation has no nonzero
fixed vectors. -/
theorem fixedSubmodule_ofMulAction_eq_bot_of_infinite [Infinite X] :
    (ofMulAction R G X).fixedSubmodule = ⊥ := by
  apply (Submodule.eq_bot_iff _).2
  intro v hv
  by_contra hv0
  have hfinite : Finite X :=
    finite_of_mem_fixedSubmodule_ofMulAction_ne_zero (G := G) v hv hv0
  exact Set.infinite_univ (Set.finite_univ_iff.mpr hfinite)

section Finite

variable [Finite X] [Nonempty X]

/-- For a finite nonempty pretransitive group action, scalars are linearly equivalent
to the fixed vectors in the permutation representation. The image of a scalar has
that scalar as its coefficient at every point. -/
noncomputable def ofMulActionFixedSubmoduleEquiv :
    R ≃ₗ[R] (ofMulAction R G X).fixedSubmodule := by
  classical
  letI := Fintype.ofFinite X
  let f : R →ₗ[R] R[X] :=
    ∑ x : X, LinearMap.toSpanSingleton R R[X] (MonoidAlgebra.single x 1)
  have hf (r : R) (a : X) : (f r).coeff a = r := by
    simp [f]
  let f₀ : R →ₗ[R] (ofMulAction R G X).fixedSubmodule :=
    f.codRestrict _ (fun r =>
      (mem_fixedSubmodule_ofMulAction_iff (R := R) (G := G) (X := X) (f r)).2
        (fun a b => by simp only [hf]))
  refine LinearEquiv.ofBijective f₀ ⟨?_, ?_⟩
  · intro r s h
    have hcoeff := congrArg
      (fun v : (ofMulAction R G X).fixedSubmodule =>
        (v : R[X]).coeff (Classical.choice ‹Nonempty X›)) h
    change (f r).coeff _ = (f s).coeff _ at hcoeff
    simpa only [hf] using hcoeff
  · intro v
    let a : X := Classical.choice ‹Nonempty X›
    refine ⟨(v : R[X]).coeff a, ?_⟩
    apply Subtype.ext
    ext b
    change (f ((v : R[X]).coeff a)).coeff b = (v : R[X]).coeff b
    rw [hf]
    exact (mem_fixedSubmodule_ofMulAction_iff (R := R) (G := G) (X := X)
      (v : R[X])).1 v.property a b

/-- The image of a scalar has that coefficient at every point of the carrier. -/
@[simp]
theorem ofMulActionFixedSubmoduleEquiv_apply_coeff (r : R) (a : X) :
    (ofMulActionFixedSubmoduleEquiv R G X r : R[X]).coeff a = r := by
  classical
  let := Fintype.ofFinite X
  change ((∑ x : X,
    LinearMap.toSpanSingleton R R[X] (MonoidAlgebra.single x 1)) r).coeff a = r
  simp

/-- The inverse of the constant-vector equivalence evaluates the coefficient at
any point of the carrier. -/
theorem ofMulActionFixedSubmoduleEquiv_symm_apply
    (v : (ofMulAction R G X).fixedSubmodule) (a : X) :
    (ofMulActionFixedSubmoduleEquiv R G X).symm v = (v : R[X]).coeff a := by
  have h := ofMulActionFixedSubmoduleEquiv_apply_coeff R G X
    ((ofMulActionFixedSubmoduleEquiv R G X).symm v) a
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end Finite

end MulAction

end Representation
