/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Cohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of monoid cohomology

Degree-zero cohomology of a linear monoid representation over an arbitrary ring
is Noetherian whenever its coefficient module is Noetherian. The proof identifies
degree zero with the fixed submodule of the original coefficient module.

For a finite monoid, each cochain module is a finite product of the coefficient
module. The cycles embed in the cochains, and cohomology is a quotient of the
cycles, so cohomology is Noetherian in every degree.

For groups over a commutative ring, these constructions agree with Mathlib's
canonical group cohomology. In that scope, the zeroth group-cohomology instance
uses Mathlib's identification with the invariant submodule and its Noetherian
submodule and linear-equivalence transport API.
-/

@[expose] public section

universe u

namespace groupCohomology

variable {R G : Type u} [CommRing R] [Group G]

/-- Zeroth group cohomology of a Noetherian coefficient representation is Noetherian. -/
instance isNoetherian_zero (A : Rep R G) [IsNoetherian R A] :
    IsNoetherian R (groupCohomology A 0) := by
  exact ((H0Iso A).toLinearEquiv.isNoetherian_iff).2 inferInstance

end groupCohomology

universe v w

namespace Rep

variable {R : Type u} {G : Type v} [Ring R] [Monoid G]

/-- Degree-zero cohomology of a Noetherian coefficient module is Noetherian,
for an arbitrary monoid and action. -/
instance isNoetherian_cohomology_zero (A : Rep.{w} R G) [IsNoetherian R A] :
    IsNoetherian R (cohomology A 0) := by
  exact ((cohomologyZeroEquiv A).isNoetherian_iff).2 inferInstance

/-- Cohomology of a finite monoid with Noetherian coefficients is Noetherian
in every degree, for an arbitrary linear action. -/
instance isNoetherian_cohomology (A : Rep.{w} R G) [Finite G] [IsNoetherian R A] (n : ℕ) :
    IsNoetherian R (cohomology A n) := by
  have : IsNoetherian R ((inhomogeneousCochains A).X n) := by
    rw [inhomogeneousCochains_X]
    infer_instance
  have : IsNoetherian R ((inhomogeneousCochains A).cycles n) :=
    isNoetherian_of_injective ((inhomogeneousCochains A).iCycles n).hom
      ((ModuleCat.mono_iff_injective ((inhomogeneousCochains A).iCycles n)).1 inferInstance)
  rw [cohomology_eq_homology]
  exact isNoetherian_of_surjective ((inhomogeneousCochains A).homologyπ n).hom
    (ModuleCat.range_eq_top_of_epi _)

end Rep
