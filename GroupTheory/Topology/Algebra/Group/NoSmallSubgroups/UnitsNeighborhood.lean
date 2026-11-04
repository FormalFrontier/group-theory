/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.Units

/-!
# Open value neighborhoods controlling subgroups of units

The topology on units remembers both the value and the opposite-valued inverse.
Subgroup inverse closure lets one intersect the two ambient neighborhoods to
obtain a single open neighborhood controlling the values of every subgroup.
-/

@[expose] public section

open Filter Set Topology MulOpposite

universe u

namespace Units

variable {D : Type u} [Monoid D] [TopologicalSpace D]

/-- The units have no small subgroups if and only if an open neighborhood of one
in the monoid contains the values of no nontrivial subgroup of units. No
continuity assumption on multiplication in the monoid is needed. -/
theorem noSmallSubgroups_iff_exists_open_subgroup_eq_bot :
    NoSmallSubgroups Dˣ ↔
      ∃ V : Set D, IsOpen V ∧ (1 : D) ∈ V ∧
        ∀ H : Subgroup Dˣ, (∀ v ∈ H, (v : D) ∈ V) → H = ⊥ := by
  constructor
  · intro hNSS
    rcases hNSS with ⟨hcontrol⟩
    rcases hcontrol with ⟨U, hU, hsmall⟩
    have hU' : U ∈ comap (embedProduct D : Dˣ → D × Dᵐᵒᵖ)
        (𝓝 (embedProduct D (1 : Dˣ))) := by
      rw [← isEmbedding_embedProduct.isInducing.nhds_eq_comap (1 : Dˣ)]
      exact hU
    rcases Filter.mem_comap.mp hU' with ⟨W, hW, hWU⟩
    have hW₁ : W ∈ 𝓝 ((1 : D), (1 : Dᵐᵒᵖ)) := by
      simpa using hW
    rw [nhds_prod_eq] at hW₁
    rcases Filter.mem_prod_iff.mp hW₁ with ⟨A, hA, B, hB, hAB⟩
    rcases mem_nhds_iff.mp hA with ⟨A₀, hA₀A, hA₀open, h1A₀⟩
    rcases mem_nhds_iff.mp hB with ⟨B₀, hB₀B, hB₀open, h1B₀⟩
    refine ⟨A₀ ∩ op ⁻¹' B₀,
      hA₀open.inter (hB₀open.preimage continuous_op), ⟨h1A₀, ?_⟩, ?_⟩
    · simpa using h1B₀
    · intro H hH
      apply hsmall H
      intro v hv
      have hvV := hH v hv
      have hiV := hH (v⁻¹) (H.inv_mem hv)
      apply hWU
      have hpair : ((v : D), op (((v⁻¹ : Dˣ) : D))) ∈ W :=
        hAB ⟨hA₀A hvV.1, hB₀B hiV.2⟩
      simpa using hpair
  · rintro ⟨V, hVopen, h1V, hcontrol⟩
    constructor
    refine ⟨(fun v : Dˣ => (v : D)) ⁻¹' V, ?_, ?_⟩
    · exact (hVopen.preimage continuous_val).mem_nhds (by simpa using h1V)
    · intro H hH
      exact hcontrol H (fun v hv => hH hv)

end Units
