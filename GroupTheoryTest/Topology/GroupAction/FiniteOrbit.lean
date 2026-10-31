/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.GroupAction.Orbit

/-!
# Finite orbits and stabilizer quotients

A finite orbit with an intrinsic T₀ topology is discrete when every group element
acts continuously on the ambient space. Continuity of the orbit map then gives
the canonical orbit–stabilizer homeomorphism. No separation condition on the
ambient space or continuity of group operations is required.
-/

universe u v

/-- Fixed-element continuity on the ambient space and continuity of the orbit map
combine to give the canonical homeomorphism for a finite T₀ orbit. -/
private theorem finiteOrbit_homeomorphQuotientStabilizer
    (G : Type u) [Group G] [TopologicalSpace G]
    {A : Type v} [TopologicalSpace A] [MulAction G A]
    (x : A) [Finite (MulAction.orbit G x)] [T0Space (MulAction.orbit G x)]
    (hfixed : ∀ g : G, Continuous (fun a : A => g • a))
    (hOrbit : Continuous (fun g : G => g • x)) :
    ∃ e : MulAction.orbit G x ≃ₜ G ⧸ MulAction.stabilizer G x,
      e.toEquiv = MulAction.orbitEquivQuotientStabilizer G x := by
  have hfixedOrbit (g : G) :
      Continuous (fun y : MulAction.orbit G x => g • y) := by
    exact ((hfixed g).comp continuous_subtype_val).subtype_mk
      (fun y => (g • y).property)
  let : DiscreteTopology (MulAction.orbit G x) :=
    MulAction.discreteTopology_of_finite_of_isPretransitive G hfixedOrbit
  exact ⟨MulAction.orbitHomeomorphQuotientStabilizer G x hOrbit, rfl⟩
