/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Finiteness of zeroth group homology

For a representation `A : Rep.{u} k G` with finite underlying carrier `A.V`, the underlying
carrier of `groupHomology.H0 A` is finite. The action is arbitrary, and neither the group nor
the coefficient ring is required to be finite. The common universe `u` for the ring, group,
and coefficient carrier follows the existing group homology API.

The proof uses the canonical quotient map `groupHomology.H0π` and its epimorphism instance
from Mathlib's `RepresentationTheory.Homological.GroupHomology.LowDegree`. Surjectivity comes
from `ModuleCat.epi_iff_surjective` in `Algebra.Category.ModuleCat.EpiMono`, and finiteness of
the image from `Finite.of_surjective` in `Data.Fintype.EquivFin`. This concerns the underlying
carrier, not finite generation as a module.

## References

* `Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree` supplies the
  canonical zeroth homology and its coefficient quotient map.
* `Mathlib.Algebra.Category.ModuleCat.EpiMono` identifies module epimorphisms with
  surjective maps.
* `Mathlib.Data.Fintype.EquivFin` provides finiteness of surjective images.
-/

@[expose] public section

universe u

namespace groupHomology

/-- Zeroth group homology of a representation with finite underlying carrier is finite. -/
instance {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) [Finite A.V] :
    Finite (groupHomology.H0 A) :=
  Finite.of_surjective (H0π A) ((ModuleCat.epi_iff_surjective (H0π A)).mp inferInstance)

end groupHomology
