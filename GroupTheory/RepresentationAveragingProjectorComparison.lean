/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.RepresentationAveragingProjector
public import Mathlib.RepresentationTheory.Invariants

/-!
# Comparison with the invariant-space averaging map

Over a commutative ring, the normalized norm `Representation.averagingProjector`
has the same underlying coefficient-linear map as Mathlib's
`Representation.averageMap`. Thus the normalized norm generalizes the existing
invariant-space averaging construction to semirings and additive commutative monoids.

The comparison is between coefficient-linear maps: `averagingProjector` is a
self-intertwiner, whereas `averageMap` is a linear endomorphism of the representation
space.

## References

This comparison uses Mathlib's constructions and API in
`Mathlib.RepresentationTheory.Invariants` and `Mathlib.RepresentationTheory.Basic`.
-/

@[expose] public section

noncomputable section

open Invertible

universe uR uG uV

namespace Representation

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [Fintype G] [AddCommGroup V] [Module R V]
variable [Invertible (Fintype.card G : R)]

/-- Mathlib's invariant-space averaging map is the norm scaled by the inverse
of the group order. -/
theorem averageMap_apply_eq_invOf_smul_norm (ρ : Representation R G V) (v : V) :
    averageMap ρ v = (⅟ (Fintype.card G : R)) • norm ρ v := by
  simp [averageMap, GroupAlgebra.average, norm]

/-- Under the hypotheses of Mathlib's invariant-space averaging construction,
the normalized norm has the same underlying coefficient-linear map. -/
theorem averagingProjector_toLinearMap_eq_averageMap (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) :
    (averagingProjector ρ h).toLinearMap = averageMap ρ := by
  ext v
  change averagingProjector ρ h v = averageMap ρ v
  apply (IsUnit.smul_bijective h).1
  change (Nat.card G : R) • averagingProjector ρ h v = (Nat.card G : R) • averageMap ρ v
  rw [natCard_smul_averagingProjector_fintype, averageMap_apply_eq_invOf_smul_norm,
    smul_smul, Nat.card_eq_fintype_card, _root_.mul_invOf_self, one_smul]

/-- The normalized norm and Mathlib's invariant-space averaging map agree on
all vectors. -/
theorem averagingProjector_apply_eq_averageMap (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v = averageMap ρ v := by
  exact congrArg (fun f : V →ₗ[R] V => f v)
    (averagingProjector_toLinearMap_eq_averageMap ρ h)

end Representation
