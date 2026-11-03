/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# No small subgroups for uniform function spaces

The group of all functions into a group with no small subgroups has no small
subgroups for the uniform-convergence topology. The domain is an arbitrary type,
with no topology. The codomain has its given uniformity and the topology induced
by that uniformity; continuity of its group operations is not required.

One entourage ball at the identity controls all evaluations simultaneously.
Every evaluation image of a subgroup in this ball is trivial, and function
extensionality makes the subgroup itself trivial.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u v

namespace UniformFun

variable {A : Type u} {D : Type v} [Group D] [UniformSpace D]

/-- The pointwise group of all functions into a group with no small subgroups
has no small subgroups for the uniform-convergence topology. -/
instance noSmallSubgroups [NoSmallSubgroups D] : NoSmallSubgroups (UniformFun A D) := by
  obtain ⟨U, hU, hUsub⟩ :=
    NoSmallSubgroups.exists_nhds_one_subgroup_eq_bot (G := D)
  rw [nhds_eq_comap_uniformity] at hU
  obtain ⟨E, hE, hEU⟩ := Filter.mem_comap.mp hU
  let V : Set (UniformFun A D) := {f | ∀ a, (1, f a) ∈ E}
  have hV : V ∈ 𝓝 (1 : UniformFun A D) := by
    have hid : Tendsto (fun f : UniformFun A D => f)
        (𝓝 (1 : UniformFun A D)) (𝓝 (1 : UniformFun A D)) := tendsto_id
    exact (UniformFun.tendsto_iff_tendstoUniformly.mp hid) E hE
  refine ⟨⟨V, hV, ?_⟩⟩
  intro H hH
  apply le_antisymm
  · intro f hf
    apply Subgroup.mem_bot.mpr
    apply UniformFun.toFun.injective
    funext a
    let ev : UniformFun A D →* D :=
      { toFun := fun g => g a
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hmap : H.map ev = ⊥ := hUsub _ (by
      intro d hd
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hd
      exact hEU ((hH hg) a))
    exact Subgroup.mem_bot.mp (hmap ▸ Subgroup.mem_map_of_mem ev hf)
  · exact bot_le

end UniformFun
