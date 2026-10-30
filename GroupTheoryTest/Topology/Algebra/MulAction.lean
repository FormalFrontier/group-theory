/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.MulAction

/-!
# Orbit maps with independently specified actions and topologies

The same-carrier examples allow an arbitrary action of a group on itself, not
necessarily its left regular action. The continuity hypothesis is on raw left
multiplication. The finite-orbit example retains any specified target topology.
-/

universe u v

example {G : Type u} [Group G] [TopologicalSpace G] [ρ : MulAction G G]
    (h_left : ∀ a : G, Continuous (fun g : G => a * g)) (x : G) :
    IsLocallyConstant (fun g : G => @SMul.smul G G ρ.toSMul g x) ↔
      IsOpen (MulAction.stabilizer G x : Set G) :=
  @MulAction.isLocallyConstant_smul_const_iff_stabilizer_isOpen G G _ _ ρ h_left x

example {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [ρ : MulAction G G] (h_left : ∀ a : G, Continuous (fun g : G => a * g)) (x : G) :
    Continuous (fun g : G => @SMul.smul G G ρ.toSMul g x) ↔
      IsOpen (MulAction.stabilizer G x : Set G) :=
  @MulAction.continuous_smul_const_iff_stabilizer_isOpen G G _ _ _ ρ _ ⟨h_left⟩ x

example {G : Type u} {X : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace X] [MulAction G X]
    (h_left : ∀ a : G, Continuous (fun g : G => a * g))
    (h_open : ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G))
    (x : X) [Finite (MulAction.orbit G x)] : Continuous (fun g : G => g • x) :=
  (MulAction.isLocallyConstant_smul_const_of_finite_orbit h_left h_open x).continuous
