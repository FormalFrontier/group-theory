/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups

/-!
# No small subgroups under open homomorphisms

An open homomorphism from a topological group with no small subgroups has a
codomain with no small subgroups if its kernel, with the induced topology, is
discrete. Continuity of the homomorphism and of the codomain operations is not
required.

For such a homomorphism continuous at the identity, no small subgroups is
equivalent for the source and codomain. Surjectivity is not required.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u v

variable {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

/-- An open homomorphism with discrete induced kernel sends no small subgroups
from a topological group to its codomain. Neither continuity of the homomorphism
nor continuity of the codomain operations is required. -/
theorem NoSmallSubgroups.of_isOpenMap [IsTopologicalGroup G] [NoSmallSubgroups G]
    (f : G →* H) [DiscreteTopology f.ker] (hf : IsOpenMap f) : NoSmallSubgroups H := by
  -- Isolate the identity in the original kernel subtype, then in the source.
  have hker : ({1} : Set f.ker) ∈ 𝓝 (1 : f.ker) :=
    (isOpen_discrete _).mem_nhds (by simp)
  obtain ⟨W, hW, hWK⟩ :=
    (mem_nhds_subtype (f.ker : Set G) (1 : f.ker) ({1} : Set f.ker)).mp hker
  have hdiff : {p : G × G | p.1⁻¹ * p.2 ∈ W} ∈ 𝓝 ((1 : G), (1 : G)) := by
    have hd : Continuous (fun p : G × G => p.1⁻¹ * p.2) :=
      continuous_fst.inv.mul continuous_snd
    exact hd.continuousAt.preimage_mem_nhds (by simpa using hW)
  rw [nhds_prod_eq] at hdiff
  obtain ⟨A₀, hA₀, B₀, hB₀, hA₀B₀⟩ := Filter.mem_prod_iff.mp hdiff
  let U : Set G := A₀ ∩ B₀
  have hU : U ∈ 𝓝 (1 : G) := inter_mem hA₀ hB₀
  have hinj : Set.InjOn f U := by
    intro x hx y hy hxy
    have hk : y⁻¹ * x ∈ f.ker := f.eq_iff.mp hxy
    have hw : y⁻¹ * x ∈ W :=
      hA₀B₀ (show (y, x) ∈ A₀ ×ˢ B₀ from ⟨hy.1, hx.2⟩)
    have hkone : (⟨y⁻¹ * x, hk⟩ : f.ker) ∈ ({1} : Set f.ker) := hWK hw
    have hval : y⁻¹ * x = 1 := congrArg Subtype.val (mem_singleton_iff.mp hkone)
    calc
      x = y * (y⁻¹ * x) := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
      _ = y := by rw [hval, mul_one]
  -- The working window must contain products and inverses inside the larger
  -- injectivity window, not necessarily inside itself.
  obtain ⟨O, hO, hOsub⟩ := NoSmallSubgroups.exists_nhds_one_subgroup_eq_bot (G := G)
  have hmul : {p : G × G | p.1 * p.2 ∈ U} ∈ 𝓝 ((1 : G), (1 : G)) := by
    have hm : Continuous (fun p : G × G => p.1 * p.2) :=
      continuous_fst.mul continuous_snd
    exact hm.continuousAt.preimage_mem_nhds (by simpa only [one_mul] using hU)
  rw [nhds_prod_eq] at hmul
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hmul
  have hUi : (fun g : G => g⁻¹) ⁻¹' U ∈ 𝓝 (1 : G) :=
    continuous_inv.continuousAt.preimage_mem_nhds (by simpa only [inv_one] using hU)
  obtain ⟨V, hVsub, hVopen, hVone⟩ := mem_nhds_iff.mp
    (inter_mem hO (inter_mem hU (inter_mem hA (inter_mem hB hUi))))
  have hVO : V ⊆ O := fun _ hx => (hVsub hx).1
  have hVU : V ⊆ U := fun _ hx => (hVsub hx).2.1
  have hVA : V ⊆ A := fun _ hx => (hVsub hx).2.2.1
  have hVB : V ⊆ B := fun _ hx => (hVsub hx).2.2.2.1
  have hVinv : ∀ ⦃x : G⦄, x ∈ V → x⁻¹ ∈ U := fun _ hx => (hVsub hx).2.2.2.2
  refine ⟨⟨f '' V, (hf V hVopen).mem_nhds ?_, ?_⟩⟩
  · exact ⟨1, hVone, map_one f⟩
  · intro S hS
    -- Every element of S already has a representative in V. Local uniqueness
    -- brings a product or inverse in U back into V, without choosing a section.
    have hlift {g : G} (hg : g ∈ U) (hfg : f g ∈ S) : g ∈ V := by
      obtain ⟨z, hz, hzg⟩ := hS hfg
      exact (hinj (hVU hz) hg hzg) ▸ hz
    let T : Subgroup G :=
      { carrier := {g | g ∈ V ∧ f g ∈ S}
        one_mem' := ⟨hVone, by simpa only [map_one] using S.one_mem⟩
        mul_mem' := by
          intro x y hx hy
          have hxy : f (x * y) ∈ S := by
            simpa only [map_mul] using S.mul_mem hx.2 hy.2
          exact ⟨hlift (hAB (show (x, y) ∈ A ×ˢ B from ⟨hVA hx.1, hVB hy.1⟩)) hxy,
            hxy⟩
        inv_mem' := by
          intro x hx
          have hxi : f (x⁻¹) ∈ S := by
            simpa only [map_inv] using S.inv_mem hx.2
          exact ⟨hlift (hVinv hx.1) hxi, hxi⟩ }
    have hT : T = ⊥ := hOsub T (fun _ hx => hVO hx.1)
    apply le_antisymm
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hS hy
      have hxT : x ∈ T := ⟨hx, hxy.symm ▸ hy⟩
      have hxone : x = 1 := Subgroup.mem_bot.mp (hT ▸ hxT)
      apply Subgroup.mem_bot.mpr
      calc
        y = f x := hxy.symm
        _ = 1 := by rw [hxone, map_one]
    · exact bot_le

/-- For an open homomorphism continuous at the identity with discrete induced
kernel, no small subgroups is equivalent for the source and codomain. The forward
implication does not use continuity at the identity. -/
theorem MonoidHom.noSmallSubgroups_iff_of_isOpenMap [IsTopologicalGroup G]
    (f : G →* H) [DiscreteTopology f.ker] (hf : IsOpenMap f) (hc : ContinuousAt f 1) :
    NoSmallSubgroups G ↔ NoSmallSubgroups H := by
  constructor
  · intro h
    let : NoSmallSubgroups G := h
    exact NoSmallSubgroups.of_isOpenMap f hf
  · intro h
    let : NoSmallSubgroups H := h
    exact NoSmallSubgroups.of_ker f hc
