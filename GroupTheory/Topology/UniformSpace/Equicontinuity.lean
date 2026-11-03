/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Equicontinuity at a common base value

When all functions in a family take the same value at a point, equicontinuity there is
equivalent to eventually mapping the whole family into each neighborhood of that value.
-/

@[expose] public section

open Filter Topology

open scoped Uniformity

universe u v w

variable {A : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace X] [UniformSpace Y]
  {F : A → X → Y} {x₀ : X} {c : Y}

/-- When every function takes the value `c` at `x₀`, equicontinuity at `x₀` is equivalent
to eventually sending the entire family into each neighborhood of `c`. -/
theorem equicontinuousAt_iff_forall_mem_nhds_of_eq (hbase : ∀ a, F a x₀ = c) :
    EquicontinuousAt F x₀ ↔ ∀ s ∈ 𝓝 c, ∀ᶠ x in 𝓝 x₀, ∀ a, F a x ∈ s := by
  constructor
  · intro h s hs
    exact (h _ (mem_nhds_uniformity_iff_right.mp hs)).mono fun x hx a =>
      hx a (hbase a)
  · intro h U hU
    exact (h _ (mem_nhds_left c hU)).mono fun x hx a => by
      simpa [hbase a] using hx a
