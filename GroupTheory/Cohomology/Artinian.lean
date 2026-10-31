/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian group cohomology

For an arbitrary group and action, ordinary degree-zero group cohomology of an
Artinian `R`-module is an Artinian `R`-module. For a finite group, the same holds
in every degree, with no restriction on the action.

## References

The proof uses Mathlib's canonical `R`-linear isomorphism from degree-zero group
cohomology to the invariant submodule, together with Mathlib's inheritance of
Artinianity by submodules and transport along linear equivalences.

In all degrees for finite groups, Mathlib's inhomogeneous cochains are finite
products of the coefficient module. The proof uses Mathlib's Artinian finite-product
instance and Homological Algebra's inheritance of Artinianity from the middle term
of a short complex to its homology.
-/

@[expose] public section

universe u

namespace groupCohomology

variable {R G : Type u} [CommRing R] [Group G]

/-- Ordinary degree-zero group cohomology of an Artinian `R`-module is Artinian,
with no restriction on the group or its action. -/
instance isArtinian_zero (A : Rep R G) [IsArtinian R A] :
    IsArtinian R (groupCohomology A 0) := by
  exact ((H0Iso A).toLinearEquiv.isArtinian_iff).2 inferInstance

/-- Ordinary cohomology of a finite group with coefficients in an Artinian `R`-module
is Artinian in every degree, for an arbitrary action. -/
instance isArtinian (A : Rep R G) [Finite G] [IsArtinian R A] (n : ℕ) :
    IsArtinian R (groupCohomology A n) := by
  have : IsArtinian R ((inhomogeneousCochains A).X n) := inferInstance
  exact @CategoryTheory.ShortComplex.isArtinian_homology_moduleCat
    R _ ((inhomogeneousCochains A).sc n) this

end groupCohomology
