/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant orbit maps and open stabilizers

An orbit map is locally constant exactly when its stabilizer is open, assuming
continuity of fixed left translations of the acting group. This needs no topology on
the acted-on set. If every finite-index subgroup is open, each finite orbit gives a
locally constant orbit map.

For a discrete target, this characterizes continuity of the orbit map. Applying the
criterion pointwise gives a characterization of joint continuity of the action.
Neither joint multiplication nor inversion continuity is required.

## References

The joint-continuity criterion generalizes `continuousSMul_iff_stabilizer_isOpen` in
`Mathlib.Topology.Algebra.MulAction`. The pointwise proof uses the open-fiber criterion
from `Mathlib.Topology.LocallyConstant.Basic`: every nonempty fiber is a left translate
of the stabilizer.
-/

@[expose] public section

open Topology

universe u v

namespace MulAction

section LocallyConstant

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace G] [MulAction G X]

/-- An orbit map is locally constant exactly when its stabilizer is open, assuming
continuity of fixed left translations. No topology on the acted-on set is needed. -/
@[to_additive
/-- An orbit map is locally constant exactly when its stabilizer is open, assuming
continuity of fixed left additions. No topology on the acted-on set is needed. -/]
theorem isLocallyConstant_smul_const_iff_stabilizer_isOpen
    (h_left : ∀ a : G, Continuous (fun g : G => a * g)) (x : X) :
    IsLocallyConstant (fun g : G => g • x) ↔ IsOpen (stabilizer G x : Set G) := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  constructor
  · intro h
    change IsOpen ((fun g : G => g • x) ⁻¹' {x})
    simpa only [one_smul] using h 1
  · intro h g₀
    have hfiber : (fun g : G => g • x) ⁻¹' {g₀ • x} =
        (fun g : G => g₀⁻¹ * g) ⁻¹' (stabilizer G x : Set G) := by
      ext g
      change (g • x = g₀ • x) ↔ (g₀⁻¹ * g) • x = x
      rw [mul_smul]
      constructor
      · intro hg
        rw [hg, ← mul_smul g₀⁻¹ g₀, inv_mul_cancel, one_smul]
      · intro hg
        have hgg := congrArg (fun y : X => g₀ • y) hg
        rw [← mul_smul g₀ g₀⁻¹, mul_inv_cancel, one_smul] at hgg
        exact hgg
    rw [hfiber]
    exact h.preimage (h_left g₀⁻¹)

/-- If every finite-index subgroup is open, a finite orbit has a locally constant
orbit map, assuming continuity of fixed left translations. -/
@[to_additive
/-- If every finite-index additive subgroup is open, a finite orbit has a locally
constant orbit map, assuming continuity of fixed left additions. -/]
theorem isLocallyConstant_smul_const_of_finite_orbit
    (h_left : ∀ a : G, Continuous (fun g : G => a * g))
    (h_open : ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G))
    (x : X) [Finite (orbit G x)] : IsLocallyConstant (fun g : G => g • x) := by
  have : Finite (G ⧸ stabilizer G x) :=
    Finite.of_equiv _ (orbitEquivQuotientStabilizer G x)
  exact (isLocallyConstant_smul_const_iff_stabilizer_isOpen h_left x).mpr
    (h_open (stabilizer G x) ⟨Nat.card_pos.ne'⟩)

end LocallyConstant

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [MulAction G X] [DiscreteTopology X]

/-- A fixed-point orbit map into a discrete space is continuous exactly when its
stabilizer is open, assuming continuity of fixed left translations on the acting group. -/
@[to_additive
/-- A fixed-point orbit map into a discrete space is continuous exactly when its
stabilizer is open, assuming continuity of fixed left additions on the acting group. -/]
theorem continuous_smul_const_iff_stabilizer_isOpen [ContinuousConstSMul G G] (x : X) :
    Continuous (fun g : G => g • x) ↔ IsOpen (stabilizer G x : Set G) := by
  rw [← IsLocallyConstant.iff_continuous]
  exact isLocallyConstant_smul_const_iff_stabilizer_isOpen
    (fun a => continuous_const_smul a) x

/-- An action on a discrete space is jointly continuous exactly when all its stabilizers
are open, assuming continuity of fixed left translations on the acting group. -/
@[to_additive
/-- An additive action on a discrete space is jointly continuous exactly when all its
stabilizers are open, assuming continuity of fixed left additions on the acting group. -/]
theorem continuousSMul_iff_stabilizer_isOpen [ContinuousConstSMul G G] :
    ContinuousSMul G X ↔ ∀ x : X, IsOpen (stabilizer G x : Set G) := by
  constructor
  · intro h x
    let : ContinuousSMul G X := h
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
