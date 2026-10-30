/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Topology.Constructions
public import GroupTheory.Topology.DenseFibers

/-!
# Coinduced topologies from cofinite spaces

A surjection with finite fibers coinduces the cofinite topology from the cofinite topology.
In contrast, a map whose every fiber is infinite coinduces the indiscrete topology. These
statements concern topology values and require no separately chosen topology on the target.

The finite-fiber argument uses Mathlib's finite-preimage and surjective-image API in both
directions. The infinite-fiber argument makes each fiber dense in the cofinite source and
applies `Function.Surjective.coinduced_eq_top_of_dense_fibers` from
`GroupTheory.Topology.DenseFibers`.
-/

@[expose] public section

open Set Topology

universe u v

namespace CofiniteTopology

/-- A surjective finite-fiber map coinduces the cofinite topology from the cofinite topology. -/
theorem coinduced_eq_cofinite_of_finite_fibers
    {X : Type u} {Y : Type v} (f : X → Y) (hf : Function.Surjective f)
    (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite) :
    TopologicalSpace.coinduced f TopologicalSpace.cofinite = TopologicalSpace.cofinite := by
  apply TopologicalSpace.ext
  funext s
  apply propext
  rw [isOpen_coinduced]
  change ((f ⁻¹' s).Nonempty → ((f ⁻¹' s)ᶜ).Finite) ↔
    (s.Nonempty → sᶜ.Finite)
  rw [← Set.preimage_compl]
  constructor
  · intro hs ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact (hs ⟨x, hy⟩).of_preimage hf
  · intro hs ⟨x, hx⟩
    exact (hs ⟨f x, hx⟩).preimage' (fun y _ => hfinite y)

/-- A map whose every fiber is infinite coinduces the indiscrete topology from the cofinite
topology. -/
theorem coinduced_eq_top_of_infinite_fibers
    {X : Type u} {Y : Type v} (f : X → Y)
    (hinfinite : ∀ y : Y, (f ⁻¹' {y}).Infinite) :
    TopologicalSpace.coinduced f TopologicalSpace.cofinite = ⊤ := by
  let : TopologicalSpace X := TopologicalSpace.cofinite
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (hinfinite y).nonempty
    exact ⟨x, hx⟩
  apply hf.coinduced_eq_top_of_dense_fibers
  intro y
  refine dense_iff_inter_open.mpr ?_
  intro U hU hne
  change U.Nonempty → Uᶜ.Finite at hU
  obtain ⟨x, hxf, hxU⟩ := (hinfinite y).exists_notMem_finite (hU hne)
  exact ⟨x, by simpa only [Set.mem_compl_iff, not_not] using hxU, hxf⟩

end CofiniteTopology
