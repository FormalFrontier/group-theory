/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian degree-zero group cohomology

For an arbitrary group and action, ordinary degree-zero group cohomology of an
Artinian `R`-module is an Artinian `R`-module.

## References

The proof uses Mathlib's canonical `R`-linear isomorphism from degree-zero group
cohomology to the invariant submodule, together with Mathlib's inheritance of
Artinianity by submodules and transport along linear equivalences.
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

end groupCohomology
