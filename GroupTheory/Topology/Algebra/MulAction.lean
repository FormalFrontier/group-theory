/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ZMod

/-!
# Discrete actions and open stabilizers

Continuity of an orbit map into a discrete space is characterized by openness of its
stabilizer when fixed left translations of the acting group are continuous. Applying
this pointwise gives a characterization of joint continuity of the action. Neither
joint multiplication nor inversion continuity is required.

## References

The joint-continuity criterion generalizes `continuousSMul_iff_stabilizer_isOpen` in
`Mathlib.Topology.Algebra.MulAction`. The pointwise proof uses the canonical stabilizer
quotient and `Subgroup.isOpen_iff_discreteTopology_quotient`.
-/

@[expose] public section

open Topology

universe u v

namespace MulAction

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [MulAction G X] [DiscreteTopology X]

/-- A fixed-point orbit map into a discrete space is continuous exactly when its
stabilizer is open, assuming continuity of fixed left translations on the acting group. -/
@[to_additive
/-- A fixed-point orbit map into a discrete space is continuous exactly when its
stabilizer is open, assuming continuity of fixed left additions on the acting group. -/]
theorem continuous_smul_const_iff_stabilizer_isOpen [ContinuousConstSMul G G] (x : X) :
    Continuous (fun g : G => g • x) ↔ IsOpen (stabilizer G x : Set G) := by
  constructor
  · intro hx
    change IsOpen ((fun g : G => g • x) ⁻¹' {x})
    exact (isOpen_discrete {x}).preimage hx
  · intro hx
    letI : DiscreteTopology (G ⧸ stabilizer G x) :=
      (Subgroup.isOpen_iff_discreteTopology_quotient (stabilizer G x)).mp hx
    have h : Continuous (ofQuotientStabilizer G x ∘
        (QuotientGroup.mk : G → G ⧸ stabilizer G x)) :=
      continuous_of_discreteTopology.comp QuotientGroup.continuous_mk
    simpa only [Function.comp_def, ofQuotientStabilizer_mk] using h

/-- An action on a discrete space is jointly continuous exactly when all its stabilizers
are open, assuming continuity of fixed left translations on the acting group. -/
@[to_additive
/-- An additive action on a discrete space is jointly continuous exactly when all its
stabilizers are open, assuming continuity of fixed left additions on the acting group. -/]
theorem continuousSMul_iff_stabilizer_isOpen [ContinuousConstSMul G G] :
    ContinuousSMul G X ↔ ∀ x : X, IsOpen (stabilizer G x : Set G) := by
  constructor
  · intro h x
    letI : ContinuousSMul G X := h
    apply (continuous_smul_const_iff_stabilizer_isOpen x).mp
    simpa only [Function.comp_def, id_eq] using
      (continuous_smul : Continuous fun p : G × X => p.1 • p.2).comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : G => x))
  · intro h
    constructor
    rw [continuous_prod_of_discrete_right]
    intro x
    exact (continuous_smul_const_iff_stabilizer_isOpen x).mpr (h x)

private theorem topologicalGroup_specialization [IsTopologicalGroup G] :
    (continuousSMul_iff_stabilizer_isOpen (G := G) (X := X)) =
      _root_.continuousSMul_iff_stabilizer_isOpen :=
  Subsingleton.elim _ _

end MulAction

private theorem zmodTwo_regularAction_nontrivial :
    (1 : ZMod 2) +ᵥ (0 : ZMod 2) ≠ 0 := by
  decide

private theorem zmodTwo_regularAction_continuous : ContinuousVAdd (ZMod 2) (ZMod 2) :=
  inferInstance

private theorem zmodTwo_pointStabilizer_isOpen :
    IsOpen (AddAction.stabilizer (ZMod 2) (0 : ZMod 2) : Set (ZMod 2)) :=
  (AddAction.continuous_vadd_const_iff_stabilizer_isOpen (0 : ZMod 2)).mp
    continuous_of_discreteTopology

private theorem zmodTwo_stabilizers_isOpen :
    ∀ x : ZMod 2, IsOpen (AddAction.stabilizer (ZMod 2) x : Set (ZMod 2)) :=
  AddAction.continuousVAdd_iff_stabilizer_isOpen.mp zmodTwo_regularAction_continuous
