/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of zeroth group cohomology

Zeroth group cohomology is a Noetherian module whenever its coefficient
representation is Noetherian, for an arbitrary group and action.

The proof uses Mathlib's canonical identification of zeroth group cohomology with
the invariant coefficient submodule, together with Mathlib's Noetherian submodule
and linear-equivalence transport API.
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
