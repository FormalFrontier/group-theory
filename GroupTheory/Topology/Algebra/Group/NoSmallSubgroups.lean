module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Separation

/-!
# Groups with no small subgroups

A group has no small subgroups if some neighborhood of the identity contains
no subgroup other than the trivial subgroup. No continuity of the group
operations is required for this definition or for its positive-powers constructor.
If inversion is continuous, the property is equivalent to a positive-powers
criterion, with an open inversion-symmetric neighborhood as witness.

For a topological group, no small subgroups implies Hausdorffness and admits a
closed identity-neighborhood containing no nontrivial subgroup. The separation
argument uses the closure of the trivial subgroup and the compatible right
uniformity of the original group topology.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe v

/-- A group has no small subgroups if some identity-neighborhood contains only
    the trivial subgroup. -/
class NoSmallSubgroups (G : Type v) [Group G] [TopologicalSpace G] : Prop where
  /-- There is an identity-neighborhood containing no nontrivial subgroup. -/
  exists_nhds_one_subgroup_eq_bot :
    ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- The defining neighborhood characterization of no small subgroups. -/
theorem noSmallSubgroups_iff :
    NoSmallSubgroups G ↔
      ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥ :=
  ⟨fun h => h.exists_nhds_one_subgroup_eq_bot, fun h => ⟨h⟩⟩

/-- An identity-neighborhood in which only the identity has all its positive
    powers implies that the group has no small subgroups. -/
theorem NoSmallSubgroups.of_nhds_one_pow {U : Set G} (hU : U ∈ 𝓝 (1 : G))
    (hpow : ∀ g : G, (∀ n : ℕ, 0 < n → g ^ n ∈ U) → g = 1) :
    NoSmallSubgroups G := by
  refine ⟨⟨U, hU, ?_⟩⟩
  intro H hH
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_bot]
    exact hpow g (fun n _ => hH (H.pow_mem hg n))
  · exact bot_le

section IsTopologicalGroup

variable [IsTopologicalGroup G]

private theorem regularSpace_of_topologicalGroup : RegularSpace G := by
  let u := IsTopologicalGroup.rightUniformSpace G
  -- The exposed construction retains the given topology, not just an equivalent one.
  have hu : u.toTopologicalSpace = ‹TopologicalSpace G› := rfl
  exact hu ▸ @UniformSpace.to_regularSpace G u

/-- A closed set containing the identity and no nontrivial subgroup forces a
    topological group to be Hausdorff. The set need not be a neighborhood. -/
theorem IsClosed.t2Space_of_subgroup_eq_bot {W : Set G} (hW : IsClosed W)
    (hW1 : (1 : G) ∈ W)
    (hsub : ∀ H : Subgroup G, (H : Set G) ⊆ W → H = ⊥) : T2Space G := by
  have hclosure : ((⊥ : Subgroup G).topologicalClosure : Set G) ⊆ W := by
    rw [Subgroup.coe_topologicalClosure_bot]
    exact closure_minimal (singleton_subset_iff.mpr hW1) hW
  have hbot := hsub (⊥ : Subgroup G).topologicalClosure hclosure
  have hclosed : IsClosed ({1} : Set G) := by
    simpa only [hbot, Subgroup.coe_bot] using
      (⊥ : Subgroup G).isClosed_topologicalClosure
  let : T1Space G := IsTopologicalGroup.t1Space G hclosed
  let : RegularSpace G := regularSpace_of_topologicalGroup
  infer_instance

/-- A topological group with no small subgroups has a closed identity-neighborhood
    containing no nontrivial subgroup. -/
theorem NoSmallSubgroups.exists_isClosed_nhds_one [NoSmallSubgroups G] :
    ∃ W ∈ 𝓝 (1 : G), IsClosed W ∧
      ∀ H : Subgroup G, (H : Set G) ⊆ W → H = ⊥ := by
  let : RegularSpace G := regularSpace_of_topologicalGroup
  obtain ⟨U, hU, hsub⟩ := NoSmallSubgroups.exists_nhds_one_subgroup_eq_bot (G := G)
  obtain ⟨W, hW, hWclosed, hWU⟩ := exists_mem_nhds_isClosed_subset hU
  exact ⟨W, hW, hWclosed, fun H hH => hsub H (hH.trans hWU)⟩

/-- A topological group with no small subgroups is Hausdorff. -/
instance (priority := 100) NoSmallSubgroups.t2Space [NoSmallSubgroups G] : T2Space G := by
  obtain ⟨W, hW, hWclosed, hsub⟩ := NoSmallSubgroups.exists_isClosed_nhds_one (G := G)
  exact hWclosed.t2Space_of_subgroup_eq_bot (mem_of_mem_nhds hW) hsub

end IsTopologicalGroup

variable [ContinuousInv G]

/-- A group with no small subgroups and continuous inversion has an open,
    inversion-symmetric identity-neighborhood in which only the identity has
    all its positive powers. -/
theorem NoSmallSubgroups.exists_open_nhds_one_pow [NoSmallSubgroups G] :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      (∀ g : G, g ∈ V ↔ g⁻¹ ∈ V) ∧
      ∀ g : G, (∀ n : ℕ, 0 < n → g ^ n ∈ V) → g = 1 := by
  obtain ⟨U, hU, hsub⟩ := (noSmallSubgroups_iff (G := G)).mp ‹NoSmallSubgroups G›
  obtain ⟨O, hOU, hO, hO1⟩ := mem_nhds_iff.mp hU
  let V : Set G := O ∩ ((fun g : G => g⁻¹) ⁻¹' O)
  have hVopen : IsOpen V := hO.inter (hO.preimage continuous_inv)
  have hV1 : (1 : G) ∈ V := ⟨hO1, by simpa using hO1⟩
  have hVinv : ∀ g : G, g ∈ V ↔ g⁻¹ ∈ V := by
    intro g
    change (g ∈ O ∧ g⁻¹ ∈ O) ↔ (g⁻¹ ∈ O ∧ (g⁻¹)⁻¹ ∈ O)
    simp only [inv_inv, and_comm]
  refine ⟨V, hVopen, hV1, hVinv, ?_⟩
  intro g hg
  have hZ : (Subgroup.zpowers g : Set G) ⊆ U := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    have hn : g ^ n ∈ V := by
      cases n with
      | ofNat n =>
          cases n with
          | zero => simpa using hV1
          | succ n =>
              change g ^ ((n + 1 : ℕ) : ℤ) ∈ V
              simpa only [zpow_natCast] using hg (n + 1) (Nat.succ_pos n)
      | negSucc n =>
          simpa only [zpow_negSucc] using
            (hVinv (g ^ (n + 1))).mp (hg (n + 1) (Nat.succ_pos n))
    exact hOU hn.1
  have hZbot : Subgroup.zpowers g = ⊥ := hsub _ hZ
  have hgZ : g ∈ Subgroup.zpowers g :=
    Subgroup.mem_zpowers_iff.mpr ⟨(1 : ℤ), by simp⟩
  have hgBot : g ∈ (⊥ : Subgroup G) := hZbot ▸ hgZ
  exact Subgroup.mem_bot.mp hgBot

/-- With continuous inversion, no small subgroups is equivalent to a
    positive-powers criterion on an identity-neighborhood. -/
theorem noSmallSubgroups_iff_exists_nhds_one_pow :
    NoSmallSubgroups G ↔
      ∃ U ∈ 𝓝 (1 : G), ∀ g : G, (∀ n : ℕ, 0 < n → g ^ n ∈ U) → g = 1 := by
  constructor
  · intro h
    let _ : NoSmallSubgroups G := h
    obtain ⟨V, hVopen, hV1, _, hVpow⟩ :=
      NoSmallSubgroups.exists_open_nhds_one_pow (G := G)
    exact ⟨V, hVopen.mem_nhds hV1, hVpow⟩
  · rintro ⟨U, hU, hpow⟩
    exact NoSmallSubgroups.of_nhds_one_pow hU hpow
