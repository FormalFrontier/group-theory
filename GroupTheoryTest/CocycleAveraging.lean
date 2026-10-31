/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.CocycleAveraging

/-! A finite affine action given by a crossed translation has a fixed point. -/

universe u v

example {G : Type u} {A : Type v} [Group G] [Finite G] [AddCommGroup A]
    [DistribMulAction G A] {z : G → A} (hz : groupCohomology.IsCocycle₁ z)
    (hN : Function.Bijective (fun a : A => Nat.card G • a)) :
    ∃ a : A, ∀ g : G, g • a + z g = a := by
  obtain ⟨v, hv⟩ := hz.exists_eq_smul_sub hN
  refine ⟨-v, ?_⟩
  intro g
  rw [smul_neg, hv]
  abel
