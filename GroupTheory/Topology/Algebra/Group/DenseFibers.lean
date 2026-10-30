/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import GroupTheory.Topology.DenseFibers

/-!
# Open subgroup comaps under homomorphisms with dense fibers

A subgroup has open comap under a group homomorphism with dense fibers exactly when it is
the whole target group. Only the source carries a topology; neither continuity of the
homomorphism nor continuity of the group operations is required. The additive result holds
for arbitrary additive groups.

The topological input is the canonical set-level principle
`Function.Surjective.isOpen_preimage_iff_of_dense_fibers` from
`GroupTheory.Topology.DenseFibers`. The subgroup criterion translates its empty-or-universal
carrier conclusion into equality with the top subgroup, using the identity to exclude the
empty case. The algebraic constructions and carrier API are supplied by Mathlib.
-/

@[expose] public section

universe u v

/-- A subgroup has open comap under a group homomorphism with dense fibers exactly when it
is the whole target group. No target topology or continuity hypotheses are needed. -/
@[to_additive
  /-- An additive subgroup has open comap under an additive group homomorphism with dense
  fibers exactly when it is the whole target group. No target topology or continuity
  hypotheses are needed. -/]
theorem Subgroup.isOpen_comap_iff_eq_top_of_dense_fibers
    {A : Type u} {B : Type v} [Group A] [Group B] [TopologicalSpace A]
    (f : A →* B) (hf : ∀ b : B, Dense {a : A | f a = b}) (K : Subgroup B) :
    IsOpen (K.comap f : Set A) ↔ K = ⊤ := by
  have : Nonempty A := ⟨1⟩
  have hsurj : Function.Surjective f := by
    intro b
    exact (hf b).nonempty
  have hpreimage : IsOpen (K.comap f : Set A) ↔
      (K : Set B) = ∅ ∨ (K : Set B) = Set.univ :=
    hsurj.isOpen_preimage_iff_of_dense_fibers hf
  constructor
  · intro hopen
    rcases hpreimage.mp hopen with hempty | huniv
    · have hmem : (1 : B) ∈ (K : Set B) := K.one_mem
      rw [hempty] at hmem
      exact False.elim hmem
    · exact SetLike.coe_injective huniv
  · intro hK
    apply hpreimage.mpr
    exact Or.inr (congrArg (fun L : Subgroup B => (L : Set B)) hK)
