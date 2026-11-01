/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Complete orthogonal idempotents in local semirings

A finite complete orthogonal family in a local semiring has exactly one unit member.
Locality supplies a unit summand, idempotence makes it one, and orthogonality makes
all the other members zero.

## References

The proof uses Mathlib's complete orthogonal families, local finite-sum criterion,
and unit-idempotent equivalence.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace CompleteOrthogonalIdempotents

variable {ι : Type u} {S : Type v} [Fintype ι] [Semiring S] [IsLocalRing S]

/-- A complete orthogonal family in a local semiring has exactly one unit member. -/
theorem existsUnique_isUnit {e : ι → S} (he : CompleteOrthogonalIdempotents e) :
    ∃! i : ι, IsUnit (e i) := by
  classical
  have hsum : IsUnit (∑ i, e i) := he.complete.symm ▸ isUnit_one
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum hsum
  have hi_one : e i = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit hi).mp (he.idem i)
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  apply hj.ne_zero
  simpa only [hi_one, mul_one] using he.ortho hji

end CompleteOrthogonalIdempotents
