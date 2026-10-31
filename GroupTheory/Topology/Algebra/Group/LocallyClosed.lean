/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Constructible
public import GroupTheory.Topology.Algebra.Group.Subgroup

/-!
# Locally closed subgroups under separate continuity

For a group with separately continuous multiplication and continuous inversion, a
subgroup is closed if and only if it is a neighborhood of the identity within its
closure. Equivalently, it is locally closed at the identity, at any specified
member, or globally locally closed. In particular, every locally constructible subgroup
is closed. The additive statements hold with separately
continuous addition and continuous negation.

No joint continuity, separation, normality or commutativity is required. All
statements use the given group operations and topology.

## Implementation notes

The proof follows Mathlib's `Subgroup.isClosed_of_isLocallyClosed`: the subgroup
is open, hence closed, in its closure. The shared construction
`Subgroup.topologicalClosureOfSeparatelyContinuousMul` supplies that closure
subgroup under the same weak continuity assumptions.

## References

* Mathlib's `Subgroup.isClosed_of_isLocallyClosed` and
  `Subgroup.isClosed_of_isLocallyClosedAt` supply the closure-subgroup argument
  and its translation to a single member.
* Mathlib's `Submonoid.topologicalClosure`, `inv_closure`,
  `Subgroup.isOpen_of_mem_nhds`, `Subgroup.isClosed_of_isOpen` and
  `isLocallyClosedAt_tfae` supply the weak-continuity and topological ingredients.
-/

@[expose] public section

open Topology
open scoped Pointwise

universe u

-- Finite Boolean combinations of open sets are decided on a dense open set.
-- Only continuity of the map is needed: constructibility of its preimages is not asserted.
private lemma exists_open_classifier {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set X} (hs : IsConstructible s) {f : Y → X}
    (hf : Continuous f) :
    ∃ U V : Set Y, IsOpen U ∧ IsOpen V ∧ Dense (U ∪ V) ∧
      U ⊆ f ⁻¹' s ∧ V ⊆ (f ⁻¹' s)ᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact W hW _ =>
      refine ⟨f ⁻¹' W, (closure (f ⁻¹' W))ᶜ, hW.preimage hf,
        isClosed_closure.isOpen_compl, ?_, subset_rfl, ?_⟩
      · intro y
        by_cases hy : y ∈ closure (f ⁻¹' W)
        · exact closure_mono Set.subset_union_left hy
        · exact subset_closure (Or.inr hy)
      · intro y hy hyW
        exact hy (subset_closure hyW)
  | union s hs t ht ihs iht =>
      obtain ⟨U, V, hU, hV, hd, hUs, hVs⟩ := ihs
      obtain ⟨U', V', hU', hV', hd', hUt, hVt⟩ := iht
      refine ⟨U ∪ U', V ∩ V', hU.union hU', hV.inter hV',
        (hd.inter_of_isOpen_left hd' (hU.union hV)).mono ?_, ?_, ?_⟩
      · intro y hy
        rcases hy with ⟨hy | hy, hy' | hy'⟩
        · exact Or.inl (Or.inl hy)
        · exact Or.inl (Or.inl hy)
        · exact Or.inl (Or.inr hy')
        · exact Or.inr ⟨hy, hy'⟩
      · rintro y (hy | hy)
        · exact Or.inl (hUs hy)
        · exact Or.inr (hUt hy)
      · rintro y ⟨hy, hy'⟩ (hys | hyt)
        · exact hVs hy hys
        · exact hVt hy' hyt
  | compl s hs ih =>
      obtain ⟨U, V, hU, hV, hd, hUs, hVs⟩ := ih
      refine ⟨V, U, hV, hU, ?_, hVs, ?_⟩
      · simpa only [Set.union_comm] using hd
      · intro y hy hys
        exact hys (hUs hy)

-- In the closure of a nonempty constructible set, the false open part is empty
-- by density, leaving a nonempty relatively open subset of the set.
private lemma exists_isLocallyClosedAt_of_isConstructible {X : Type*}
    [TopologicalSpace X] {s : Set X} (hs : IsConstructible s) (hne : s.Nonempty) :
    ∃ x ∈ s, IsLocallyClosedAt s x := by
  obtain ⟨U, V, hU, hV, hd, hUs, hVs⟩ :=
    exists_open_classifier hs (continuous_subtype_val : Continuous (Subtype.val : closure s → X))
  have hds : Dense ((Subtype.val : closure s → X) ⁻¹' s) := by
    rw [Subtype.dense_iff]
    have heq : (Subtype.val : closure s → X) ''
        ((Subtype.val : closure s → X) ⁻¹' s) = s := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
    rw [heq]
  have hVe : V = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨z, hzs, hzV⟩ := hds.exists_mem_open hV ⟨y, hy⟩
    exact hVs hzV hzs
  rw [hVe, Set.union_empty] at hd
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, _⟩ := hd.exists_mem_open isOpen_univ
    (show (Set.univ : Set (closure s)).Nonempty from ⟨⟨x, subset_closure hx⟩, Set.mem_univ _⟩)
  obtain ⟨W, hW, hWU⟩ := IsInducing.subtypeVal.isOpen_iff.mp hU
  have hyW : (y : X) ∈ W := by
    change y ∈ (Subtype.val : closure s → X) ⁻¹' W
    rwa [hWU]
  refine ⟨y, hUs hy, isLocallyClosedAt_iff_exists_inter_closure_subset.mpr
    ⟨W, hW.mem_nhds hyW, ?_⟩⟩
  rintro z ⟨hzW, hzs⟩
  apply hUs (show (⟨z, hzs⟩ : closure s) ∈ U from ?_)
  rw [← hWU]
  exact hzW

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A subgroup is closed exactly when it is a neighborhood of the identity within
its closure. Separate continuity of multiplication and continuity of inversion
suffice; the neighborhood is not required to be an ambient neighborhood. -/
@[to_additive
/-- An additive subgroup is closed exactly when it is a neighborhood of zero
within its closure. Separate continuity of addition and continuity of negation
suffice; the neighborhood is not required to be an ambient neighborhood. -/]
theorem isClosed_iff_mem_nhdsWithin_one [SeparatelyContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) :
    IsClosed (H : Set G) ↔ (H : Set G) ∈ 𝓝[_root_.closure (H : Set G)] (1 : G) := by
  constructor
  · intro hH
    rw [hH.closure_eq]
    exact self_mem_nhdsWithin
  · intro hH
    let K := H.topologicalClosureOfSeparatelyContinuousMul
    have hHK : H ≤ K := H.le_topologicalClosureOfSeparatelyContinuousMul
    let : SeparatelyContinuousMul K :=
      IsInducing.separatelyContinuousMul K.subtype ⟨rfl⟩
    let V : Subgroup K := H.subgroupOf K
    have hV : (V : Set K) ∈ 𝓝 (1 : K) :=
      preimage_coe_mem_nhds_subtype.mpr hH
    have hclosed : IsClosed (V : Set K) :=
      V.isClosed_of_isOpen (V.isOpen_of_mem_nhds hV)
    have hemb : IsClosedEmbedding K.subtype :=
      H.isClosed_topologicalClosureOfSeparatelyContinuousMul.isClosedEmbedding_subtypeVal
    rwa [hemb.isClosed_iff_image_isClosed, ← coe_map,
      map_subgroupOf_eq_of_le hHK] at hclosed

/-- A subgroup is closed exactly when it is locally closed at the identity,
assuming separately continuous multiplication and continuous inversion. -/
@[to_additive
/-- An additive subgroup is closed exactly when it is locally closed at zero,
assuming separately continuous addition and continuous negation. -/]
theorem isClosed_iff_isLocallyClosedAt_one [SeparatelyContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) : IsClosed (H : Set G) ↔ IsLocallyClosedAt (H : Set G) (1 : G) :=
  H.isClosed_iff_mem_nhdsWithin_one.trans
    ((isLocallyClosedAt_tfae (H : Set G) (1 : G)).out 1 8).symm

/-- A subgroup is closed exactly when it is locally closed at a specified member.
Membership is essential: local closedness outside the closure is automatic. -/
@[to_additive
/-- An additive subgroup is closed exactly when it is locally closed at a specified
member. Membership is essential: local closedness outside the closure is automatic. -/]
theorem isClosed_iff_isLocallyClosedAt [SeparatelyContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) {x : G} (hx : x ∈ H) :
    IsClosed (H : Set G) ↔ IsLocallyClosedAt (H : Set G) x := by
  constructor
  · exact fun hH ↦ hH.isLocallyClosed.isLocallyClosedAt hx
  · intro hH
    have htrans : (fun y : G ↦ x * y) ⁻¹' (H : Set G) = H := by
      ext y
      exact H.mul_mem_cancel_left hx
    have hlocal : IsLocallyClosedAt (H : Set G) (x * 1) := by simpa using hH
    have hlocalOne := hlocal.preimage (continuous_const_mul x)
    rw [htrans] at hlocalOne
    exact H.isClosed_iff_isLocallyClosedAt_one.mpr hlocalOne

/-- A locally closed subgroup is closed when multiplication is separately
continuous and inversion is continuous. This generalizes Mathlib's
`Subgroup.isClosed_of_isLocallyClosed` on the same group and topology. -/
@[to_additive
/-- A locally closed additive subgroup is closed when addition is separately
continuous and negation is continuous. This generalizes Mathlib's
`AddSubgroup.isClosed_of_isLocallyClosed` on the same group and topology. -/]
theorem isClosed_iff_isLocallyClosed [SeparatelyContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) : IsClosed (H : Set G) ↔ IsLocallyClosed (H : Set G) := by
  constructor
  · exact IsClosed.isLocallyClosed
  · intro hH
    exact H.isClosed_iff_isLocallyClosedAt_one.mpr (hH.isLocallyClosedAt H.one_mem)

/-- A locally constructible subgroup is closed when multiplication is separately
continuous and inversion is continuous. No separation or Noetherian hypothesis
on the ambient space is needed. -/
@[to_additive
/-- A locally constructible additive subgroup is closed when addition is separately
continuous and negation is continuous. No separation or Noetherian hypothesis
on the ambient space is needed. -/]
theorem isClosed_of_isLocallyConstructible [SeparatelyContinuousMul G] [ContinuousInv G]
    (H : Subgroup G) (hH : IsLocallyConstructible (H : Set G)) :
    IsClosed (H : Set G) := by
  obtain ⟨U, hUnhds, hU, hHU⟩ := hH (1 : G)
  obtain ⟨x, hx, hlocal⟩ := exists_isLocallyClosedAt_of_isConstructible hHU
    ⟨⟨1, mem_of_mem_nhds hUnhds⟩, H.one_mem⟩
  apply (H.isClosed_iff_isLocallyClosedAt hx).mpr
  rw [isLocallyClosedAt_iff_coborder_mem_nhds] at hlocal ⊢
  rw [hU.isOpenEmbedding_subtypeVal.coborder_preimage] at hlocal
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hlocal
  exact Filter.mem_of_superset
    ((hU.isOpenMap_subtype_val V hV).mem_nhds ⟨x, hxV, rfl⟩)
    (Set.image_subset_iff.mpr hVsub)

/-- Under joint continuity, the closedness implication agrees with Mathlib's
locally closed subgroup theorem for the identical subgroup, operations and topology. -/
@[to_additive
/-- Under joint continuity, the closedness implication agrees with Mathlib's
locally closed additive subgroup theorem for the identical subgroup, operations
and topology. -/]
theorem isClosed_iff_isLocallyClosed_mpr_eq [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsLocallyClosed (H : Set G)) :
    H.isClosed_iff_isLocallyClosed.mpr hH = H.isClosed_of_isLocallyClosed hH :=
  Subsingleton.elim _ _

end Subgroup
