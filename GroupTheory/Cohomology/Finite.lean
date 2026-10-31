/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Finiteness of group cohomology

Zeroth group cohomology has finite underlying carrier when the coefficient representation
has finite underlying carrier, for an arbitrary group and action. For a finite group,
ordinary group cohomology has finite underlying carrier in every nonnegative degree.
The coefficient ring need not be finite.

The degree-zero result uses Mathlib's identification with the invariant coefficient
submodule. The all-degree result uses finite inhomogeneous cochains and the finiteness
of homology for a short complex of modules with finite middle carrier.
-/

@[expose] public section

open CategoryTheory

universe u

namespace groupCohomology

variable {R G : Type u} [CommRing R] [Group G]

/-- Zeroth group cohomology has finite underlying carrier for finite coefficients. -/
instance finite_zero (A : Rep R G) [Finite A] : Finite (groupCohomology A 0) :=
  Finite.of_equiv _
    (((CategoryTheory.forget (ModuleCat R)).mapIso (H0Iso A)).toEquiv.symm)

/-- Ordinary cohomology has finite carrier for a finite group and finite coefficient carrier. -/
instance finite {R G : Type u} [CommRing R] [Group G]
    (A : Rep.{u} R G) [Finite G] [Finite A] (n : ℕ) : Finite (groupCohomology A n) := by
  change Finite (((inhomogeneousCochains A).sc n).homology)
  have : Finite ((inhomogeneousCochains A).X n) := by
    dsimp [inhomogeneousCochains]
    infer_instance
  exact @ShortComplex.finite_homology_moduleCat R _ ((inhomogeneousCochains A).sc n) this

end groupCohomology
