/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import GroupTheory.Topology.Algebra.Group.Units

/-!
# Separation of spaces of continuous homomorphisms

For a group and a monoid with arbitrary topologies, fixed-point evaluation in
the canonical space of units is continuous. Hausdorffness of the
units therefore makes the compact-open homomorphism space Hausdorff. In particular,
a monoid with continuous multiplication and closed identity singleton has this
property; no continuity of the source group operations is required.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G]
  [Monoid D] [TopologicalSpace D]

/-- Evaluation at a fixed group element, followed by the algebraic lift to units, is
continuous in the compact-open topology. No continuity of the group operations is needed. -/
theorem continuous_toHomUnits_eval (g : G) :
    Continuous (fun f : G →ₜ* D => f.toMonoidHom.toHomUnits g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simpa [Function.comp_def] using
      (continuous_eval_const g : Continuous (fun f : G →ₜ* D => f g))
  · simp only [← map_inv, MonoidHom.coe_toHomUnits]
    simpa using
      (continuous_eval_const (g⁻¹) : Continuous (fun f : G →ₜ* D => f (g⁻¹)))

/-- The compact-open space of continuous homomorphisms from a group to a monoid is
Hausdorff if the monoid's canonical space of units is Hausdorff. -/
theorem t2Space_of_t2Space_units [T2Space Dˣ] : T2Space (G →ₜ* D) := by
  refine T2Space.of_injective_continuous
    (f := fun f : G →ₜ* D => fun g : G => f.toMonoidHom.toHomUnits g) ?_ ?_
  · intro f f' h
    apply ContinuousMonoidHom.ext
    intro g
    simpa using
      congrArg (fun k : G → Dˣ => (k g : D)) h
  · exact continuous_pi fun g => continuous_toHomUnits_eval g

/-- A closed identity singleton in a monoid with continuous multiplication makes its
compact-open space of continuous homomorphisms from any topologized group Hausdorff. -/
theorem t2Space_of_isClosed_one [ContinuousMul D]
    (hOne : IsClosed ({1} : Set D)) : T2Space (G →ₜ* D) := by
  let _ : T2Space Dˣ := Units.t2Space_of_isClosed_one hOne
  exact t2Space_of_t2Space_units (G := G) (D := D)

end ContinuousMonoidHom
