/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Constructions

/-!
# Subgroup control by value neighbourhoods

When a group's topology is induced by its value and inverse-value coordinates, an open
neighbourhood of the identity's value can control subgroups uniformly. The units specialization
uses the canonical units topology of a monoid equipped with an arbitrary topology.
-/

@[expose] public section

open MulOpposite

universe u v

/-- Open value neighbourhoods control subgroups. -/
theorem Topology.IsInducing.exists_isOpen_value_subgroup_subset
    {U : Type u} {D : Type v} [Group U] [TopologicalSpace U] [TopologicalSpace D]
    {f : U → D} (hf : Topology.IsInducing (fun x : U => (f x, op (f x⁻¹))))
    {W : Set U} (hW : W ∈ nhds (1 : U)) :
    ∃ V : Set D, IsOpen V ∧ f 1 ∈ V ∧
      ∀ H : Subgroup U, (∀ x ∈ H, f x ∈ V) → (H : Set U) ⊆ W := by
  rcases mem_nhds_iff.mp hW with ⟨s, hsW, hs, h1⟩
  rcases hf.isOpen_iff.mp hs with ⟨t, ht, rfl⟩
  rcases mem_nhds_prod_iff'.mp (ht.mem_nhds h1) with ⟨A, B, hA, ha, hB, hb, hAB⟩
  refine ⟨A ∩ op ⁻¹' B, hA.inter (hB.preimage continuous_op), ⟨ha, by simpa using hb⟩, ?_⟩
  exact fun H hH x hx => hsW (hAB ⟨(hH x hx).1, (hH x⁻¹ (H.inv_mem hx)).2⟩)

/-- Open value neighbourhoods control subgroups of units. -/
theorem Units.exists_isOpen_val_subgroup_subset
    {D : Type v} [Monoid D] [TopologicalSpace D]
    {W : Set Dˣ} (hW : W ∈ nhds (1 : Dˣ)) :
    ∃ V : Set D, IsOpen V ∧ (1 : D) ∈ V ∧
      ∀ H : Subgroup Dˣ, (∀ x ∈ H, (x : D) ∈ V) → (H : Set Dˣ) ⊆ W := by
  simpa only [Units.val_one] using
    (Topology.IsInducing.exists_isOpen_value_subgroup_subset
      (f := fun x : Dˣ => (x : D))
      (Units.isInducing_embedProduct (M := D)) hW)
