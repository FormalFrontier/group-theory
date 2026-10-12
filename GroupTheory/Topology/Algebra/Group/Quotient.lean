/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
public import GroupTheory.Topology.Algebra.ConstMulAction

/-!
# Subgroups and the topology of left-coset quotients

For an arbitrary subgroup `H`, openness is equivalent to discreteness of the
canonical left-coset quotient `G ⧸ H`, and closedness is equivalent to its T1
separation property, when fixed left translations are continuous. An open
subgroup is clopen without an index assumption. At finite index, openness,
closedness and clopenness are equivalent. Compactness is needed only to deduce
finite index from openness. Neither normality, right-translation continuity,
joint multiplication, continuous inversion nor ambient separation is assumed.
Fixed left actions on the canonical quotient inherit continuity from the source,
for every subgroup; the additive quotient has the corresponding fixed-addition
instance.

## Implementation notes

The quotient and its coinduced topology are Mathlib's existing objects. A singleton
fiber over the class of `g` is the left coset `g • H`; `IsOpen.smul`, `IsClosed.smul`
and the coinducing projection relate subgroup properties to quotient singletons.
A finite T1 space is discrete. These facts do not require the stronger
arbitrary-subgroup open-projection theorem, whose right-saturation argument
requires right translations.

## References

* Mathlib's `QuotientGroup.eq_class_eq_leftCoset`, `QuotientGroup.preimage_mk_one`,
  `QuotientGroup.isQuotientMap_mk`, `IsOpen.smul`, `IsClosed.smul`,
  `Finite.instDiscreteTopology` and compact-discrete finiteness.
* Mathlib's `QuotientGroup.discreteTopology_iff`, `QuotientGroup.t1Space_iff`,
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.isOpen_of_isClosed_of_finiteIndex`
  and `Subgroup.isClosed_of_isOpen` provide separately continuous specializations.
-/

@[expose] public section

open scoped Pointwise

universe u

namespace QuotientGroup

/-- Fixed left multiplication induces continuous fixed actions on the canonical
left-coset quotient by any subgroup. This extends Mathlib's
`QuotientGroup.instContinuousConstSMul` from separately continuous multiplication
without changing the quotient, its action or its topology. -/
@[to_additive
/-- Fixed left addition induces continuous fixed actions on the canonical coset
quotient by any additive subgroup. This extends Mathlib's
`QuotientAddGroup.instContinuousConstVAdd` from separately continuous addition
without changing the quotient, its action or its topology. -/]
instance (priority := 100) continuousConstSMul
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) : ContinuousConstSMul G (G ⧸ H) := by
  exact Topology.IsCoinducing.continuousConstSMul
    { toFun := (QuotientGroup.mk : G → G ⧸ H)
      map_smul' := fun g x => (MulAction.Quotient.smul_mk H g x).symm }
    (QuotientGroup.isQuotientMap_mk H).isCoinducing

/-- The fixed-action continuity instance agrees with Mathlib's separately
continuous provider on the same canonical left-coset quotient. -/
@[to_additive
/-- The fixed-addition continuity instance agrees with Mathlib's separately
continuous provider on the same canonical coset quotient. -/]
theorem continuousConstSMul_eq
    {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (H : Subgroup G) :
    continuousConstSMul H =
      (QuotientGroup.instContinuousConstSMul (N := H) : ContinuousConstSMul G (G ⧸ H)) := by
  exact Subsingleton.elim _ _

end QuotientGroup

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

/-- A subgroup is closed exactly when its canonical left-coset quotient is T1,
assuming continuity of fixed left translations. No finite-index, compactness,
normality or ambient separation assumption is needed. This extends Mathlib's
`QuotientGroup.t1Space_iff` from separately continuous multiplication. -/
theorem isClosed_iff_t1Space_quotient (H : Subgroup G) :
    IsClosed (H : Set G) ↔ T1Space (G ⧸ H) := by
  constructor
  · intro hH
    refine ⟨?_⟩
    refine QuotientGroup.mk_surjective.forall.2 fun g ↦ ?_
    apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage.mp
    have hfiber : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {QuotientGroup.mk g} =
        g • (H : Set G) := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        QuotientGroup.eq_class_eq_leftCoset H g
    rw [hfiber]
    exact hH.smul g
  · intro hQ
    let : T1Space (G ⧸ H) := hQ
    rw [← QuotientGroup.preimage_mk_one H]
    exact (isClosed_singleton (x := (QuotientGroup.mk : G → G ⧸ H) 1)).preimage
      QuotientGroup.continuous_mk

/-- A subgroup is clopen exactly when it is open, assuming continuity of fixed
left translations. No finite-index or compactness assumption is needed. The
open-to-closed implication extends Mathlib's `Subgroup.isClosed_of_isOpen` from
separately continuous multiplication. -/
theorem isClopen_iff_isOpen (H : Subgroup G) :
    IsClopen (H : Set G) ↔ IsOpen (H : Set G) := by
  constructor
  · exact fun hH ↦ hH.isOpen
  · intro hH
    let : DiscreteTopology (G ⧸ H) := (H.isOpen_iff_discreteTopology_quotient).mp hH
    exact ⟨(H.isClosed_iff_t1Space_quotient).mpr inferInstance, hH⟩

/-- A finite-index subgroup is open exactly when it is closed, assuming continuity
of fixed left translations. Compactness and normality are not required. The
closed-to-open implication extends Mathlib's
`Subgroup.isOpen_of_isClosed_of_finiteIndex` from separately continuous multiplication. -/
theorem isOpen_iff_isClosed (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H : Set G) ↔ IsClosed (H : Set G) := by
  constructor
  · intro hH
    exact ((H.isClopen_iff_isOpen).mpr hH).isClosed
  · intro hH
    let : T1Space (G ⧸ H) := (H.isClosed_iff_t1Space_quotient).mp hH
    let : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact (H.isOpen_iff_discreteTopology_quotient).mpr Finite.instDiscreteTopology

/-- A finite-index subgroup is clopen exactly when it is closed, assuming continuity
of fixed left translations. Compactness, normality and ambient separation are not
required. This combines the closed-to-open implication of Mathlib's
`Subgroup.isOpen_of_isClosed_of_finiteIndex` with the definition of clopenness. -/
theorem isClopen_iff_isClosed (H : Subgroup G) [H.FiniteIndex] :
    IsClopen (H : Set G) ↔ IsClosed (H : Set G) := by
  exact (H.isClopen_iff_isOpen).trans H.isOpen_iff_isClosed

end Subgroup
