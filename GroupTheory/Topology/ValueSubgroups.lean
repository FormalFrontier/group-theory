/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Topology.Algebra.Constructions

/-!
# Subgroup control by value neighbourhoods

When a group's topology is induced by its value and inverse-value coordinates, an open
neighbourhood of the identity's value can control subgroups uniformly. The units specialization
uses the canonical units topology of a monoid equipped with an arbitrary topology.

For a homomorphism from a group, `MonoidHom.mapsTo_iff_eq_one_of_subgroup_values`
characterizes when a subgroup has all its values in a set controlling unit subgroups.
-/

@[expose] public section

open MulOpposite

universe u v w

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

/-- If all unit subgroups valued in `V` are trivial, mapping into `V` means being killed. -/
public theorem MonoidHom.mapsTo_iff_eq_one_of_subgroup_values
    {G : Type*} {D : Type*} [Group G] [Monoid D] (f : G →* D)
    (H : Subgroup G) (V : Set D) (h1 : 1 ∈ V)
    (hV : ∀ K : Subgroup Dˣ, Set.MapsTo Units.val K V → K = ⊥) :
    Set.MapsTo f H V ↔ ∀ x ∈ H, f x = 1 := by
  constructor
  · intro hf x hx
    let K := H.map f.toHomUnits
    have hK : K = ⊥ := hV K (by
      rintro u ⟨y, hy, rfl⟩
      exact hf hy)
    have hxK : f.toHomUnits x ∈ K := ⟨x, hx, rfl⟩
    rw [hK] at hxK
    exact congrArg Units.val hxK
  · intro hf x hx
    simpa only [hf x hx] using h1

/-- A homomorphism maps a subgroup into a set containing one and controlling unit subgroups
if and only if it is trivial on that subgroup. -/
theorem mapsTo_iff_eq_one_of_subgroup_values {G : Type u} {D : Type v} {F : Type w}
    [Group G] [Monoid D] [FunLike F G D] [MonoidHomClass F G D] (f : F)
    (H : Subgroup G) (V : Set D) (h1 : 1 ∈ V)
    (hV : ∀ K : Subgroup Dˣ, Set.MapsTo Units.val K V → K = ⊥) :
    Set.MapsTo f H V ↔ ∀ x ∈ H, f x = 1 := by
  exact MonoidHom.mapsTo_iff_eq_one_of_subgroup_values
    (MonoidHomClass.toMonoidHom f) H V h1 hV
