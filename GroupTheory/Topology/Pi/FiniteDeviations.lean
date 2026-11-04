/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions

/-!
# Finite deviations in product spaces

A family in a dependent product converges along the cofinite filter to a base point
if, in each coordinate, only finitely many terms differ from that point. Its range
together with the base point is compact. The time type is arbitrary, and no
separation hypothesis is needed on the coordinate spaces.
-/

@[expose] public section

open Filter Set

universe u v w

namespace Pi

variable {I : Type u} {T : Type v} {X : I → Type w}
    [∀ i, TopologicalSpace (X i)] {b : (i : I) → X i} {x : T → (i : I) → X i}

/-- Finitely many deviations in each coordinate imply cofinite convergence in the product. -/
theorem tendsto_cofinite_of_finite_ne
    (h : ∀ i, Set.Finite {t : T | x t i ≠ b i}) :
    Tendsto x cofinite (nhds b) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : (fun t : T => x t i) =ᶠ[cofinite] (fun _ : T => b i) :=
    Filter.eventually_cofinite.mpr (h i)
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

/-- A family with finitely many deviations in each coordinate has compact range
when its base point is included. -/
theorem isCompact_insert_range_of_finite_ne
    (h : ∀ i, Set.Finite {t : T | x t i ≠ b i}) :
    IsCompact (insert b (Set.range x)) := by
  exact Filter.Tendsto.isCompact_insert_range_of_cofinite
    (tendsto_cofinite_of_finite_ne h)

end Pi
