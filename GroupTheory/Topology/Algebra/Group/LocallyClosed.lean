/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Locally closed subgroups under separate continuity

For a group with separately continuous multiplication and continuous inversion, a
subgroup is closed if and only if it is a neighborhood of the identity within its
closure. Equivalently, it is locally closed at the identity, at any specified
member, or globally locally closed. The additive statements hold with separately
continuous addition and continuous negation.

No joint continuity, separation, normality or commutativity is required. All
statements use the given group operations and topology.

## Implementation notes

The proof follows Mathlib's `Subgroup.isClosed_of_isLocallyClosed`: the subgroup
is open, hence closed, in its closure. The closure carrier is supplied by
`Submonoid.topologicalClosure`; `inv_closure` makes it a subgroup locally in the
proof. No additional public closure construction is introduced.

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
    let K : Subgroup G :=
      { H.toSubmonoid.topologicalClosure with
        inv_mem' := by
          intro x hx
          change x ∈ (_root_.closure (H : Set G))⁻¹
          rwa [inv_closure, inv_coe_set] }
    have hHK : H ≤ K := _root_.subset_closure
    let : SeparatelyContinuousMul K :=
      IsInducing.separatelyContinuousMul K.subtype ⟨rfl⟩
    let V : Subgroup K := H.subgroupOf K
    have hV : (V : Set K) ∈ 𝓝 (1 : K) :=
      preimage_coe_mem_nhds_subtype.mpr hH
    have hclosed : IsClosed (V : Set K) :=
      V.isClosed_of_isOpen (V.isOpen_of_mem_nhds hV)
    have hemb : IsClosedEmbedding K.subtype :=
      isClosed_closure.isClosedEmbedding_subtypeVal
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
