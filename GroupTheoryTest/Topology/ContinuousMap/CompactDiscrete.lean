/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.ContinuousMap.CompactDiscrete
import Mathlib.Topology.Order

/-!
# Isolated maps and continuous observers on a compact-open map space

The identity map on the two-point discrete space takes distinct values and is
isolated in the compact-open topology. Every observer on this map space is
continuous, even when no continuity condition is imposed on the observer.
An empty-domain example checks the boundary case.
-/

namespace GroupTheoryTest.Topology.ContinuousMap.CompactDiscrete

private def booleanIdentity : C(Bool, Bool) := ⟨id, continuous_id⟩

example : booleanIdentity false ≠ booleanIdentity true := by
  decide

example : booleanIdentity ≠ ContinuousMap.const Bool false := by
  intro h
  have hvalue : true = false := congrArg (fun f : C(Bool, Bool) => f true) h
  cases hvalue

example : IsOpen ({booleanIdentity} : Set C(Bool, Bool)) := by
  let : DiscreteTopology C(Bool, Bool) := ContinuousMap.discreteTopology_of_compactSpace
  exact isOpen_discrete _

example : Continuous (fun f : C(Bool, Bool) => f false && f true) := by
  let : DiscreteTopology C(Bool, Bool) := ContinuousMap.discreteTopology_of_compactSpace
  exact continuous_of_discreteTopology

example {X : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace X] [DiscreteTopology Y] (observer : C(X, Y) → Z) :
    Continuous observer := by
  let : DiscreteTopology C(X, Y) := ContinuousMap.discreteTopology_of_compactSpace
  exact continuous_of_discreteTopology

example : IsOpen ({ContinuousMap.id Empty} : Set C(Empty, Empty)) := by
  let : DiscreteTopology C(Empty, Empty) := ContinuousMap.discreteTopology_of_compactSpace
  exact isOpen_discrete _

end GroupTheoryTest.Topology.ContinuousMap.CompactDiscrete
