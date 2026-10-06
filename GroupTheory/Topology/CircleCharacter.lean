/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.OpenKernel
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Finite images of circle-valued characters

The open centered half-circle is a subgroup-free neighborhood of the identity.
Consequently, continuous circle-valued characters of compact nonarchimedean groups
have finite image, without an abelian or finite-generation assumption.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  remarks following Theorem (1.1.11), for the compact totally disconnected case.
* Mathlib's `Circle.isOpen_centeredArc` and
  `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two`.
-/

@[expose] public section

open Filter
open scoped Topology Real

universe u

namespace Circle

/-- The open centered half-circle contains no nontrivial subgroup. -/
theorem subgroup_eq_bot_of_subset_centeredArc_pi_div_two (H : Subgroup Circle)
    (hH : (H : Set Circle) ⊆ centeredArc (π / 2)) : H = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  exact eq_one_of_forall_pow_mem_centeredArc_pi_div_two (by
    intro n hn
    exact hH (H.pow_mem hz n))

/-- The centered half-circle is a subgroup-free identity neighborhood. -/
theorem centeredArc_pi_div_two_mem_nhds_one : centeredArc (π / 2) ∈ 𝓝 (1 : Circle) := by
  apply (isOpen_centeredArc _).mem_nhds
  refine ⟨0, by simp [Real.pi_pos], by simp⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- Circle-valued characters from nonarchimedean groups have open kernel. -/
theorem isOpen_ker (f : G →ₜ* Circle) : IsOpen (f.toMonoidHom.ker : Set G) := by
  exact f.isOpen_ker_of_subgroup_free_nhds _ centeredArc_pi_div_two_mem_nhds_one
    subgroup_eq_bot_of_subset_centeredArc_pi_div_two

/-- A continuous circle-valued character on a compact nonarchimedean group
has finite image. -/
theorem finite_range [CompactSpace G] (f : G →ₜ* Circle) : (Set.range f).Finite := by
  exact f.finite_range_of_subgroup_free_nhds _ centeredArc_pi_div_two_mem_nhds_one
    subgroup_eq_bot_of_subset_centeredArc_pi_div_two

/-- The locally compact totally disconnected version follows from the
compact-open-subgroup neighborhood basis. -/
theorem isOpen_ker_of_locallyCompact_totallyDisconnected
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (f : G →ₜ* Circle) : IsOpen (f.toMonoidHom.ker : Set G) := by
  exact @isOpen_ker G _ _ (NonarchimedeanGroup.of_locallyCompact_totallyDisconnected G) f

/-- Continuous circle-valued characters of compact, locally compact, totally
disconnected groups have finite image. No source commutativity or separate
Hausdorff hypothesis is needed. -/
theorem finite_range_of_compact_locallyCompact_totallyDisconnected
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (f : G →ₜ* Circle) : (Set.range f).Finite := by
  exact @finite_range G _ _ (NonarchimedeanGroup.of_locallyCompact_totallyDisconnected G) _ f

end Circle

end
