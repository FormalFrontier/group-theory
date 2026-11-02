/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups

/-!
# No small subgroups in product groups

A product of groups has no small subgroups exactly when every factor has no small
subgroups and only finitely many factors are nontrivial. The product carries its
pointwise group structure and the product topology of the given factor topologies.
No continuity of the group operations is required.

In particular, a finite product of groups with no small subgroups has no small
subgroups. The characterization includes empty products and products whose factors
are all trivial, even when the index type is infinite.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u v

variable {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- A product of groups has no small subgroups if and only if every factor has no
small subgroups and only finitely many factors are nontrivial. -/
theorem noSmallSubgroups_pi_iff :
    NoSmallSubgroups (∀ i, G i) ↔
      (∀ i, NoSmallSubgroups (G i)) ∧ Set.Finite {i | ¬ Subsingleton (G i)} := by
  classical
  -- Insertion at one coordinate is continuous independently of the group operations.
  let e : ∀ i, G i →* ∀ j, G j := fun i =>
    { toFun := fun x => Function.update 1 i x
      map_one' := by
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Function.update, h]
      map_mul' := by
        intro x y
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Function.update, h] }
  have he : ∀ i, Continuous (e i) := by
    intro i
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      have hei : (fun x : G i => (e i x) i) = id := by
        funext x
        simp [e]
      rw [hei]
      exact continuous_id
    · have hej : (fun x : G i => (e i x) j) = fun _ => (1 : G j) := by
        funext x
        simp [e, Function.update, h]
      rw [hej]
      exact continuous_const
  constructor
  · intro h
    let : NoSmallSubgroups (∀ i, G i) := h
    obtain ⟨U, hU, hsub⟩ := (noSmallSubgroups_iff (G := ∀ i, G i)).mp h
    constructor
    · intro i
      apply NoSmallSubgroups.of_injective (e i) (he i).continuousAt
      intro x y hxy
      simpa [e] using congrArg (fun z => z i) hxy
    · have hex : ∀ i, ∃ x : G i, ¬ Subsingleton (G i) → e i x ∉ U := by
        intro i
        by_cases hi : Subsingleton (G i)
        · exact ⟨1, fun hn => (hn hi).elim⟩
        · by_contra hn
          have hall : ∀ x : G i, e i x ∈ U := by
            intro x
            by_contra hx
            exact hn ⟨x, fun _ => hx⟩
          have hmap : (⊤ : Subgroup (G i)).map (e i) = ⊥ := hsub _ (by
            intro y hy
            rcases Subgroup.mem_map.mp hy with ⟨x, _, rfl⟩
            exact hall x)
          have hone : ∀ x : G i, x = 1 := by
            intro x
            have hxmap : e i x ∈ (⊤ : Subgroup (G i)).map (e i) :=
              Subgroup.mem_map.mpr ⟨x, Subgroup.mem_top x, rfl⟩
            have hxone : e i x = 1 := Subgroup.mem_bot.mp (hmap ▸ hxmap)
            simpa [e] using congrArg (fun y => y i) hxone
          exact hi ⟨fun x y => (hone x).trans (hone y).symm⟩
      choose x hx using hex
      let f : ι → ∀ i, G i := fun i => e i (x i)
      -- Each fixed coordinate is eventually one along the cofinite filter.
      have hf : Tendsto f cofinite (𝓝 (1 : ∀ i, G i)) := by
        apply tendsto_pi_nhds.mpr
        intro j
        have hne : ∀ᶠ i in (cofinite : Filter ι), j ≠ i := by
          apply Filter.eventually_cofinite.mpr
          simp
        apply tendsto_const_nhds.congr'
        filter_upwards [hne] with i hi
        simp [f, e, hi]
      have hfinite : Set.Finite {i | f i ∉ U} :=
        Filter.eventually_cofinite.mp (hf.eventually hU)
      exact hfinite.subset (fun i hi => hx i hi)
  · rintro ⟨h, hs⟩
    choose U hU hsub using fun i => (noSmallSubgroups_iff (G := G i)).mp (h i)
    let s : Finset ι := hs.toFinset
    have hs_mem : ∀ i, i ∈ s ↔ ¬ Subsingleton (G i) := by
      intro i
      simp [s]
    -- Only the finitely many nontrivial coordinates need controlling neighborhoods.
    have hnhds : Set.pi (↑s) U ∈ 𝓝 (1 : ∀ i, G i) := by
      rw [nhds_pi]
      exact Filter.mem_pi'.mpr ⟨s, U, hU, fun _ hx => hx⟩
    refine (noSmallSubgroups_iff (G := ∀ i, G i)).mpr ⟨Set.pi (↑s) U, hnhds, ?_⟩
    intro H hH
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      funext i
      by_cases hi : i ∈ s
      · let p : (∀ j, G j) →* G i :=
          { toFun := fun y => y i
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have hmap : H.map p = ⊥ := hsub i _ (by
          intro y hy
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          exact hH hz i hi)
        have hxmap : p x ∈ H.map p := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        exact Subgroup.mem_bot.mp (hmap ▸ hxmap)
      · have htriv : Subsingleton (G i) := by
          by_contra hn
          exact hi ((hs_mem i).mpr hn)
        exact @Subsingleton.elim (G i) htriv (x i) 1
    · exact bot_le

/-- A finite product of groups with no small subgroups has no small subgroups. -/
instance NoSmallSubgroups.pi [Finite ι] [∀ i, NoSmallSubgroups (G i)] :
    NoSmallSubgroups (∀ i, G i) := by
  exact noSmallSubgroups_pi_iff.mpr ⟨fun _ => inferInstance, Set.toFinite _⟩
