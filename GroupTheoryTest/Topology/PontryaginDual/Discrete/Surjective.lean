/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.PontryaginDual.Discrete.Surjective
import Mathlib.GroupTheory.Perm.Basic

/-!
# Evaluation on the discrete symmetric group on three letters

A character of the dual of the noncommutative symmetric group on three letters
is evaluation at a permutation. This uses surjectivity through its public API
and does not require a commutative group structure on the source.
-/

@[expose] public section

local instance : TopologicalSpace (Equiv.Perm (Fin 3)) := ⊥

local instance : DiscreteTopology (Equiv.Perm (Fin 3)) :=
  discreteTopology_bot _

example (χ : PontryaginDual (PontryaginDual (Equiv.Perm (Fin 3)))) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ ψ : PontryaginDual (Equiv.Perm (Fin 3)),
      χ ψ = ψ σ := by
  obtain ⟨σ, hσ⟩ :=
    PontryaginDual.eval_surjective_of_discrete (Equiv.Perm (Fin 3)) χ
  refine ⟨σ, fun ψ => ?_⟩
  rw [← hσ, PontryaginDual.eval_apply]
