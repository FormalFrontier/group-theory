/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.CocycleAveraging

/-! The inverse-unit average is the fixed point for the associated affine action. -/

open scoped BigOperators

universe u v w

example {G : Type u} {A : Type v} {R : Type w} [Group G] [Fintype G]
    [Semiring R] [AddCommGroup A] [Module R A] [DistribMulAction G A]
    {z : G → A} (hz : groupCohomology.IsCocycle₁ z)
    (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) :
    ∀ g : G, g • ((↑(u⁻¹) : R) • (∑ h : G, z h)) + z g =
      (↑(u⁻¹) : R) • (∑ h : G, z h) := by
  intro g
  have hg := hz.eq_smul_sub_inv_smul_sum u hu g
  rw [smul_neg] at hg
  rw [hg]
  abel
