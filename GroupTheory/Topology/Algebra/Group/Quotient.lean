/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Open subgroups and discrete left-coset quotients

For an arbitrary subgroup `H`, openness is equivalent to discreteness of the
canonical left-coset quotient `G ⧸ H` when fixed left translations are continuous.
Compactness is needed only for the finite-index consequence. Neither normality,
right-translation continuity, joint multiplication, continuous inversion nor
separation is assumed.

## Implementation notes

The quotient and its coinduced topology are Mathlib's existing objects. A singleton
fiber over the class of `g` is the left coset `g • H`; `IsOpen.smul` and the
coinducing projection give the intended discreteness argument. This does not use
the stronger arbitrary-subgroup open-projection theorem, whose right-saturation
argument requires right translations.

## References

* Mathlib's `QuotientGroup.eq_class_eq_leftCoset`, `QuotientGroup.preimage_mk_one`,
  `QuotientGroup.isQuotientMap_mk`, `IsOpen.smul` and compact-discrete finiteness.
* Mathlib's `QuotientGroup.discreteTopology_iff` and
  `Subgroup.quotient_finite_of_isOpen` give the stronger, separately continuous
  specializations. These statements are candidates for generalizing those APIs;
  the clients include agreement lemmas under the original hypotheses.

No external source-text correspondence is asserted.
-/

@[expose] public section

open scoped Pointwise

universe u

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- A subgroup is open exactly when its canonical left-coset quotient is discrete,
assuming only continuity of fixed left translations. Compactness and normality
are not required. The supplied quotient topology is unchanged. -/
theorem isOpen_iff_discreteTopology_quotient (H : Subgroup G) :
    IsOpen (H : Set G) ↔ DiscreteTopology (G ⧸ H) := by
  constructor
  · intro hH
    refine discreteTopology_iff_isOpen_singleton.mpr ?_
    refine QuotientGroup.mk_surjective.forall.2 fun g ↦ ?_
    apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isOpen_preimage.mp
    have hfiber : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {QuotientGroup.mk g} =
        g • (H : Set G) := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        QuotientGroup.eq_class_eq_leftCoset H g
    rw [hfiber]
    exact hH.smul g
  · intro hQ
    let : DiscreteTopology (G ⧸ H) := hQ
    rw [← QuotientGroup.preimage_mk_one H]
    exact (isOpen_discrete _).preimage QuotientGroup.continuous_mk

/-- An open subgroup of a compact group equipped with a topology has finite index
if fixed left translations are continuous. No joint multiplication, continuous
inversion, right translations, separation or normality is required. -/
theorem finiteIndex_of_isOpen [CompactSpace G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  let : DiscreteTopology (G ⧸ H) := (H.isOpen_iff_discreteTopology_quotient).mp hH
  let : Finite (G ⧸ H) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

end Subgroup
