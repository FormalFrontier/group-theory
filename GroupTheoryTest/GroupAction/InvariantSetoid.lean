/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.GroupAction.InvariantSetoid
public import GroupTheoryTest.GroupAction.RestrictedCoset

/-!
# Invariant relations on cosets in the three-point permutation group

Take `H = ⊥` and the nonnormal subgroup fixing `2` in `Equiv.Perm (Fin 3)`.
The model relation is defined directly as the kernel of the canonical map `G/H → G/K`,
independently of the correspondence. Its identity and crossing points are unrelated.
The crossing point and its translate by `flip` lie in the same restricted left `K`-orbit,
but are unrelated by the kernel. Thus restricted orbit equivalence is not a replacement
for the invariant relation classified by the correspondence.

The nonnormal subgroup and distinct image cosets are reused from the
`ThreePointCosets` model in `GroupTheoryTest.GroupAction.RestrictedCoset`.
-/

@[expose] public section

namespace ThreePointCosetRelations

open ThreePointCosets

/-- The permutation group of three points. -/
abbrev G := Equiv.Perm (Fin 3)

/-- The subgroup at the source of the model's quotient map. -/
abbrev H : Subgroup G := ⊥

/-- The stock left coset space at the trivial subgroup. -/
abbrev X := G ⧸ H

/-- The identity point of the source coset space. -/
def identityPoint : X := QuotientGroup.mk (1 : G)

/-- The crossing point of the source coset space. -/
def crossingPoint : X := QuotientGroup.mk crossing

/-- The translate of the crossing point by the nonidentity element fixing `2`. -/
def flippedPoint : X := ThreePointCosets.flip • crossingPoint

/-- The canonical equivariant map in this closed model. -/
def projection : X →[G] G ⧸ pointStabilizer :=
  MulActionHom.quotientMapOfLE (bot_le : H ≤ pointStabilizer)

/-- The model relation, defined as a function kernel without using the correspondence. -/
def relation : Setoid X := Setoid.ker projection

/-- The direct kernel as a left-invariant equivalence relation. -/
def invariantRelation : MulAction.InvariantSetoid G X :=
  ⟨relation, by
    intro g x y hxy
    change projection x = projection y at hxy
    change projection (g • x) = projection (g • y)
    simpa only [map_smul] using congrArg (fun z : G ⧸ pointStabilizer => g • z) hxy⟩

/-- Kernel membership in the model is equality of canonical images. -/
theorem relation_iff (x y : X) : relation x y ↔ projection x = projection y :=
  Iff.rfl

/-- The underlying relation of the invariant model is the independently defined kernel. -/
@[simp] theorem invariantRelation_val : invariantRelation.1 = relation :=
  rfl

/-- Representatives are sent to their classes modulo the point stabilizer. -/
@[simp] theorem projection_mk (g : G) :
    projection (QuotientGroup.mk g) = (QuotientGroup.mk g : G ⧸ pointStabilizer) :=
  MulActionHom.quotientMapOfLE_apply_mk (bot_le : H ≤ pointStabilizer) g

/-- The model's identity point maps to the public identity coset. -/
@[simp] theorem projection_identityPoint : projection identityPoint = identityCoset :=
  rfl

/-- The model's crossing point maps to the public crossing coset. -/
@[simp] theorem projection_crossingPoint : projection crossingPoint = crossingCoset :=
  rfl

/-- Equivariance sends the flipped point to the third public coset. -/
@[simp] theorem projection_flippedPoint : projection flippedPoint = thirdCoset := by
  change projection ((flip : G) • crossingPoint) = (flip : G) • crossingCoset
  rw [map_smul, projection_crossingPoint]

/-- The model retains the nonnormality of the public point stabilizer. -/
theorem intermediate_not_normal : ¬ pointStabilizer.Normal :=
  pointStabilizer_not_normal

/-- The two source points have distinct canonical images. -/
theorem images_distinct : projection identityPoint ≠ projection crossingPoint :=
  cosets_distinct.1

/-- There is more than one class in the direct kernel. -/
theorem not_related_identity_crossing : ¬ relation identityPoint crossingPoint := by
  exact fun h => images_distinct ((relation_iff _ _).mp h)

/-- The flipped point is in the same restricted left orbit as the crossing point. -/
theorem flippedPoint_mem_orbit :
    flippedPoint ∈ MulAction.orbit pointStabilizer crossingPoint :=
  ⟨flip, rfl⟩

/-- The same restricted-orbit pair has distinct kernel images. -/
theorem not_related_crossing_flipped : ¬ relation crossingPoint flippedPoint := by
  intro h
  apply cosets_distinct.2.2
  simpa only [projection_crossingPoint, projection_flippedPoint] using (relation_iff _ _).mp h

/-- The direct kernel differs from the restricted left orbit equivalence relation. -/
theorem relation_ne_restrictedOrbitRel : relation ≠ MulAction.orbitRel pointStabilizer X := by
  intro h
  have hrel : relation flippedPoint crossingPoint := by
    rw [h]
    exact MulAction.orbitRel_apply.mpr flippedPoint_mem_orbit
  exact not_related_crossing_flipped (relation.symm' hrel)

/-- The basepoint block of the independent invariant model is not the entire coset space. -/
theorem baseBlock_ne_univ :
    (MulAction.InvariantSetoid.toBlock invariantRelation identityPoint).1 ≠ Set.univ := by
  intro h
  have hm : crossingPoint ∈
      (MulAction.InvariantSetoid.toBlock invariantRelation identityPoint).1 := by
    rw [h]
    exact Set.mem_univ _
  exact not_related_identity_crossing (relation.symm' hm)

/-- The point stabilizer as an overgroup of the stabilizer of the source identity point. -/
def overgroup : Set.Ici (MulAction.stabilizer G identityPoint) :=
  ⟨pointStabilizer, (MulAction.stabilizer_quotient H).le.trans bot_le⟩

/-- The intermediate subgroup is the public point stabilizer, not an assumed subgroup. -/
@[simp] theorem overgroup_val : overgroup.1 = pointStabilizer :=
  rfl

/-- The correspondence specializes to the independently constructed model kernel. -/
theorem correspondence_relation :
    (MulAction.stabilizerInvariantSetoidOrderIso G identityPoint overgroup).1 = relation :=
  MulAction.stabilizerInvariantSetoidOrderIso_quotient_ker (bot_le : H ≤ pointStabilizer)

/-- The correspondence value has distinct classes in this nonnormal example. -/
theorem correspondence_not_related :
    ¬ (MulAction.stabilizerInvariantSetoidOrderIso G identityPoint overgroup).1
      identityPoint crossingPoint := by
  rw [correspondence_relation]
  exact not_related_identity_crossing

/-- Applying the inverse correspondence to the independent kernel recovers the subgroup. -/
theorem recovered_subgroup :
    ((MulAction.stabilizerInvariantSetoidOrderIso G identityPoint).symm invariantRelation).1 =
      pointStabilizer := by
  have hmodel : MulAction.stabilizerInvariantSetoidOrderIso G identityPoint overgroup =
      invariantRelation := Subtype.ext correspondence_relation
  have hrecover :=
    (MulAction.stabilizerInvariantSetoidOrderIso G identityPoint).symm_apply_apply overgroup
  rw [hmodel] at hrecover
  exact congrArg Subtype.val hrecover

end ThreePointCosetRelations
