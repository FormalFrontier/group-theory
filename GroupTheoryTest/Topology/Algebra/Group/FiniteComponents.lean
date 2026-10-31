/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.Subgroup
import GroupTheory.Topology.Algebra.MulAction.IrreducibleComponents

/-!
# Identity components from finitely many irreducible components

The topological finite-component theorem supplies the local finiteness evidence
needed by the subgroup API, without strengthening the continuity assumptions.
-/

open Topology

universe u

example {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (hfin : (irreducibleComponents G).Finite) :
    IsOpen (Subgroup.connectedComponentOfOneOfContinuousConstSMul G : Set G) ∧
      (Subgroup.connectedComponentOfOneOfContinuousConstSMul G).FiniteIndex := by
  let := TopologicalSpace.finite_connectedComponents_of_finite_irreducibleComponents hfin
  exact ⟨Subgroup.isOpen_connectedComponentOfOneOfContinuousConstSMul, inferInstance⟩
