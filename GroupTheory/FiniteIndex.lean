/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Finite index and full rank in finitely generated abelian groups

For a finitely generated abelian group, a subgroup has finite index exactly when it has the
same integer-module rank as the ambient group. Neither the ambient group nor the subgroup
is assumed to be free or torsion-free.

## Main results

* `Submodule.isTorsion_quotient_iff_finrank_eq`: over a commutative domain, a quotient of a
  finitely generated module is torsion exactly when the submodule has full rank.
* `Submodule.finite_quotient_iff_finrank_eq`: an integer-module quotient is finite exactly
  when the submodule has full rank, generalizing `Submodule.finiteQuotient_iff` beyond free
  modules.
* `AddSubgroup.finiteIndex_iff_finrank_eq`: the corresponding finite-index criterion for
  additive subgroups.
* `Submodule.finite_quotient_span_range_of_linearIndependent` and
  `AddSubgroup.index_span_range_pos_of_linearIndependent`: the span of a linearly independent
  family of full rank has finite quotient and positive subgroup index.

The integer-module criteria use the canonical structures attached to the additive
commutative groups. In particular, they also apply to finite groups of rank zero.

## References

These results generalize Mathlib's `Submodule.finiteQuotient_iff` using its
`Submodule.finrank_quotient_add_finrank`, `Module.finrank_eq_zero_iff_isTorsion`, and
`Module.finite_of_fg_torsion`. The full-rank span criteria also use Mathlib's
`finrank_span_eq_card` and `AddSubgroup.index_ne_zero_iff_finite`.
-/

@[expose] public section

universe u v

variable {M : Type v} [AddCommGroup M]

namespace Submodule

section CommRing

variable {R : Type u} [CommRing R] [IsDomain R] [Module R M] [Module.Finite R M]

/-- Over a commutative domain, a quotient of a finitely generated module is torsion if and
only if the submodule has the same rank as the ambient module. -/
theorem isTorsion_quotient_iff_finrank_eq (L : Submodule R M) :
    Module.IsTorsion R (M ⧸ L) ↔ Module.finrank R L = Module.finrank R M := by
  rw [← Module.finrank_eq_zero_iff_isTorsion]
  constructor
  · intro h
    simpa only [h, zero_add] using L.finrank_quotient_add_finrank
  · intro h
    exact Nat.add_right_cancel
      ((L.finrank_quotient_add_finrank.trans h.symm).trans (zero_add _).symm)

end CommRing

variable [Module.Finite ℤ M]

/-- A submodule of a finitely generated abelian group has finite quotient if and only if it
has the same integer-module rank as the ambient group. No freeness assumption is needed. -/
theorem finite_quotient_iff_finrank_eq (L : Submodule ℤ M) :
    Finite (M ⧸ L) ↔ Module.finrank ℤ L = Module.finrank ℤ M := by
  rw [← L.isTorsion_quotient_iff_finrank_eq]
  constructor
  · intro h
    let : Finite (M ⧸ L) := h
    exact isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite
  · exact Module.finite_of_fg_torsion (M ⧸ L)

/-- The span of a linearly independent family with as many elements as the integer-module
rank has finite quotient, without a freeness assumption on the ambient group. -/
theorem finite_quotient_span_range_of_linearIndependent
    (e : Fin (Module.finrank ℤ M) → M) (he : LinearIndependent ℤ e) :
    Finite (M ⧸ span ℤ (Set.range e)) := by
  apply (finite_quotient_iff_finrank_eq (span ℤ (Set.range e))).2
  simpa only [Fintype.card_fin] using finrank_span_eq_card he

/-- The finite-quotient criterion specializes to Mathlib's free-module criterion. -/
private theorem finiteQuotient_iff_eq_finite_quotient_iff_finrank_eq [Module.Free ℤ M]
    (L : Submodule ℤ M) :
    finiteQuotient_iff L = finite_quotient_iff_finrank_eq L :=
  Subsingleton.elim _ _

end Submodule

namespace AddSubgroup

variable [Module.Finite ℤ M]

/-- An additive subgroup of a finitely generated abelian group has finite index if and only
if it has the same integer-module rank as the ambient group. -/
theorem finiteIndex_iff_finrank_eq (H : AddSubgroup M) :
    H.FiniteIndex ↔ Module.finrank ℤ H = Module.finrank ℤ M := by
  rw [finiteIndex_iff_finite_quotient]
  exact H.toIntSubmodule.finite_quotient_iff_finrank_eq

/-- The span of a linearly independent family with as many elements as the integer-module
rank has positive additive-subgroup index, including in rank zero. -/
theorem index_span_range_pos_of_linearIndependent
    (e : Fin (Module.finrank ℤ M) → M) (he : LinearIndependent ℤ e) :
    0 < (Submodule.span ℤ (Set.range e)).toAddSubgroup.index := by
  apply Nat.pos_of_ne_zero
  exact index_ne_zero_iff_finite.mpr
    (Submodule.finite_quotient_span_range_of_linearIndependent e he)

end AddSubgroup
