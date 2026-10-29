/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Maps.Basic

/-!
# Descent of openness of finite-index subgroups

The condition that every finite-index subgroup is open descends along homomorphisms
that reflect open preimages, in particular along quotient maps, surjective open maps,
and homomorphisms admitting a continuous right-inverse function. The section need not
be a homomorphism, and the given topologies need not make either group a topological group.

The proofs use Mathlib's relative-index comap and topological-map APIs. The pullback
argument follows the relative-index method used by this library's automatic-continuity
results. Additive versions are obtained from the same proofs.
-/

@[expose] public section

open Topology

universe u v

namespace Subgroup

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Openness of all finite-index subgroups descends along a homomorphism that reflects
openness of preimages of all subsets. Neither continuity nor surjectivity is required. -/
@[to_additive]
theorem isOpen_finiteIndex_of_reflectsOpenPreimage (r : G →* H)
    (hr : ∀ U : Set H, IsOpen (r ⁻¹' U) → IsOpen U)
    (hG : ∀ N : Subgroup G, N.FiniteIndex → IsOpen (N : Set G)) :
    ∀ N : Subgroup H, N.FiniteIndex → IsOpen (N : Set H) := by
  intro N hN
  have : N.FiniteIndex := hN
  have hrel : (N.comap r).IsFiniteRelIndex (⊤ : Subgroup G) := by
    simpa using IsFiniteRelIndex.comap r
      (show N.IsFiniteRelIndex (⊤ : Subgroup H) from isFiniteRelIndex_of_finiteIndex)
  exact hr N (hG (N.comap r) (isFiniteRelIndex_top_iff.mp hrel))

/-- Openness of all finite-index subgroups descends along a homomorphism with a
continuous right-inverse function. No algebraic structure on the section is required. -/
@[to_additive]
theorem isOpen_finiteIndex_of_continuous_section (r : G →* H) (s : H → G)
    (hs : Continuous s) (hrs : ∀ h, r (s h) = h)
    (hG : ∀ N : Subgroup G, N.FiniteIndex → IsOpen (N : Set G)) :
    ∀ N : Subgroup H, N.FiniteIndex → IsOpen (N : Set H) := by
  apply isOpen_finiteIndex_of_reflectsOpenPreimage r ?_ hG
  intro U hU
  have heq : s ⁻¹' (r ⁻¹' U) = U := by
    ext h
    change r (s h) ∈ U ↔ h ∈ U
    rw [hrs]
  rw [← heq]
  exact hU.preimage hs

/-- Openness of all finite-index subgroups descends along a quotient-map homomorphism. -/
@[to_additive]
theorem isOpen_finiteIndex_of_isQuotientMap (r : G →* H) (hr : IsQuotientMap r)
    (hG : ∀ N : Subgroup G, N.FiniteIndex → IsOpen (N : Set G)) :
    ∀ N : Subgroup H, N.FiniteIndex → IsOpen (N : Set H) := by
  exact isOpen_finiteIndex_of_reflectsOpenPreimage r
    (fun _ hU => hr.isOpen_preimage.mp hU) hG

/-- Openness of all finite-index subgroups descends along a surjective open
homomorphism, without assuming its continuity. -/
@[to_additive]
theorem isOpen_finiteIndex_of_surjective_isOpenMap (r : G →* H)
    (hr : Function.Surjective r) (ho : IsOpenMap r)
    (hG : ∀ N : Subgroup G, N.FiniteIndex → IsOpen (N : Set G)) :
    ∀ N : Subgroup H, N.FiniteIndex → IsOpen (N : Set H) := by
  apply isOpen_finiteIndex_of_reflectsOpenPreimage r ?_ hG
  intro U hU
  rw [← Set.image_preimage_eq U hr]
  exact ho _ hU

/-- Every finite-index subgroup of a canonical normal quotient is open if every
finite-index subgroup of the original group is open. The normal subgroup need not
be closed or open, and the original group need not be a topological group. -/
@[to_additive]
theorem isOpen_finiteIndex_quotient (N : Subgroup G) [N.Normal]
    (hG : ∀ K : Subgroup G, K.FiniteIndex → IsOpen (K : Set G)) :
    ∀ K : Subgroup (G ⧸ N), K.FiniteIndex → IsOpen (K : Set (G ⧸ N)) := by
  exact isOpen_finiteIndex_of_reflectsOpenPreimage (QuotientGroup.mk' N)
    (fun _ hU => hU) hG

/-- Openness of all finite-index subgroups is invariant under a multiplicative
homeomorphism between the given topological spaces. -/
@[to_additive]
theorem isOpen_finiteIndex_iff_of_mulHomeomorph (e : G ≃ₜ* H) :
    (∀ N : Subgroup G, N.FiniteIndex → IsOpen (N : Set G)) ↔
      ∀ N : Subgroup H, N.FiniteIndex → IsOpen (N : Set H) := by
  constructor
  · exact isOpen_finiteIndex_of_continuous_section e.toMonoidHom e.symm
      e.symm.continuous e.apply_symm_apply
  · exact isOpen_finiteIndex_of_continuous_section e.symm.toMonoidHom e
      e.continuous e.symm_apply_apply

end Subgroup
