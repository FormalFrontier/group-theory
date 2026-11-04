/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Equicontinuity

/-!
# Equicontinuity in left-uniform groups

The pointwise criterion expresses equicontinuity of arbitrary families using uniform
control of left differences. It specializes Mathlib's target-basis criterion using
the characteristic left uniformity and the neighborhood filter at the identity.
-/

@[expose] public section

open Filter Topology

universe u v w

/-- Equicontinuity into a left-uniform group is uniform control of left differences at the point. -/
theorem equicontinuousAt_iff_forall_mem_nhds_inv_mul
    {I : Type u} {X : Type v} {D : Type w} [TopologicalSpace X] [Group D]
    [UniformSpace D] [IsLeftUniformGroup D] (F : I → X → D) (x : X) :
    EquicontinuousAt F x ↔
      ∀ V ∈ 𝓝 (1 : D), ∀ᶠ y in 𝓝 x, ∀ i, (F i x)⁻¹ * F i y ∈ V := by
  have h := (𝓝 (1 : D)).basis_sets.comap (fun p : D × D => p.1⁻¹ * p.2)
  rw [← uniformity_eq_comap_inv_mul_nhds_one] at h
  exact h.equicontinuousAt_iff_right
