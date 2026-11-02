/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Finite-coordinate factorization into groups with no small subgroups

A homomorphism from a product of groups to a group with no small subgroups,
continuous at the identity, kills the subgroup whose coordinates are one on some
finite set. The product has its pointwise group structure and the product topology;
no continuity of the group operations is needed.

Composing a continuous homomorphism with extension by the identity gives
finite-factor data. If the coordinate kernel is killed, composing this factor with
coordinate restriction recovers the original homomorphism. The factor is unique for
the fixed set of coordinates. The construction uses only monoids with arbitrary
topologies; global continuity is needed for the bundled continuous factor, not for
the coordinate-kernel conclusion.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u v w

variable {ι : Type u} {G : ι → Type v} {D : Type w}

attribute [local instance] Classical.propDecidable

namespace ContinuousMonoidHom

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- The finite-coordinate factor obtained by extending by the identity and then
applying the given continuous homomorphism. -/
noncomputable def finiteCoordinateFactor (f : (∀ i, G i) →ₜ* D) (s : Finset ι) :
    (∀ i : {i // i ∈ s}, G i) →ₜ* D :=
  { toFun := fun x => f (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
    map_one' := by
      have h : (fun i => if hi : i ∈ s then
          (1 : ∀ j : {i // i ∈ s}, G j) ⟨i, hi⟩ else 1) = (1 : ∀ i, G i) := by
        funext i
        simp
      rw [h]
      exact map_one f
    map_mul' := by
      intro x y
      have h : (fun i => if hi : i ∈ s then (x * y) ⟨i, hi⟩ else 1) =
          (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1) *
            (fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 1) := by
        funext i
        by_cases hi : i ∈ s <;> simp [hi]
      rw [h]
      exact map_mul f
        (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
        (fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 1)
    continuous_toFun := f.continuous.comp (by
      apply continuous_pi
      intro i
      by_cases hi : i ∈ s
      · simpa only [dite_eq_left hi] using
          (continuous_apply (⟨i, hi⟩ : {i // i ∈ s}))
      · simpa only [dite_eq_right hi] using
          (continuous_const :
            Continuous (fun _ : ∀ j : {i // i ∈ s}, G j => (1 : G i)))) }

@[simp]
theorem finiteCoordinateFactor_apply (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (x : ∀ i : {i // i ∈ s}, G i) :
    f.finiteCoordinateFactor s x =
      f (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1) := rfl

/-- A factor through a fixed coordinate restriction is necessarily the
finite-coordinate factor obtained by extension by the identity. -/
theorem finiteCoordinateFactor_unique (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (g : (∀ i : {i // i ∈ s}, G i) →ₜ* D)
    (hg : ∀ x : ∀ i, G i, f x = g (fun i => x i)) :
    g = f.finiteCoordinateFactor s := by
  apply DFunLike.ext
  intro x
  rw [finiteCoordinateFactor_apply]
  have hx := hg (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
  have he : (fun i : {i // i ∈ s} =>
      if hi : (i : ι) ∈ s then x ⟨i, hi⟩ else 1) = x := by
    funext i
    simp only [dite_eq_left i.property]
  simpa only [he] using hx.symm

end Monoid

end ContinuousMonoidHom

section Group

variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D]

/-- A homomorphism continuous at the identity into a group with no small subgroups
kills the subgroup whose coordinates are one on some finite set. -/
theorem MonoidHom.exists_finset_coordinateKernel_le_ker (f : (∀ i, G i) →* D)
    (hf : ContinuousAt f 1) [NoSmallSubgroups D] :
    ∃ s : Finset ι, Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.ker := by
  obtain ⟨U, hU, hUsub⟩ := (noSmallSubgroups_iff (G := D)).mp inferInstance
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.preimage_mem_nhds (by simpa only [map_one] using hU)
  rw [nhds_pi] at hpre
  obtain ⟨s, V, hV, hVU⟩ := Filter.mem_pi'.mp hpre
  refine ⟨s, ?_⟩
  have hmap : (Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i)))).map f = ⊥ :=
    hUsub _ (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      apply hVU
      intro i hi
      have hxi : x i = 1 := Subgroup.mem_bot.mp (hx i hi)
      rw [hxi]
      exact mem_of_mem_nhds (hV i))
  intro x hx
  exact MonoidHom.mem_ker.mpr
    (Subgroup.mem_bot.mp (hmap ▸ Subgroup.mem_map_of_mem f hx))

/-- A homomorphism continuous at the identity into a group with no small subgroups
is one on every product element that is one on a suitable finite set of coordinates. -/
theorem MonoidHom.exists_finset_eq_one_of_coordinates_eq_one (f : (∀ i, G i) →* D)
    (hf : ContinuousAt f 1) [NoSmallSubgroups D] :
    ∃ s : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 := by
  obtain ⟨s, hs⟩ := f.exists_finset_coordinateKernel_le_ker hf
  refine ⟨s, fun x hx => MonoidHom.mem_ker.mp (hs ?_)⟩
  intro i hi
  exact Subgroup.mem_bot.mpr (hx i hi)

namespace ContinuousMonoidHom

/-- If a continuous homomorphism kills a coordinate kernel, its finite-coordinate
factor recovers it after restriction to those coordinates. -/
theorem finiteCoordinateFactor_restrict (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker)
    (x : ∀ i, G i) : f.finiteCoordinateFactor s (fun i => x i) = f x := by
  rw [finiteCoordinateFactor_apply]
  let y : ∀ i, G i := fun i =>
    if hi : i ∈ s then (fun j : {i // i ∈ s} => x j) ⟨i, hi⟩ else 1
  have hx : x * y⁻¹ ∈ Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) := by
    intro i hi
    apply Subgroup.mem_bot.mpr
    have hi' : i ∈ s := hi
    have hyi : y i = x i := by simp only [y, dite_eq_left hi']
    change x i * (y i)⁻¹ = 1
    rw [hyi, mul_inv_cancel]
  have hfx := MonoidHom.mem_ker.mp (hs hx)
  have hxy : f x = f y := mul_inv_eq_one.mp (by
    simpa using hfx)
  exact hxy.symm

/-- Factorization as an equality of functions through the coordinate restriction. -/
theorem eq_finiteCoordinateFactor_comp_restrict (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker) :
    (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  funext x
  exact (f.finiteCoordinateFactor_restrict s hs x).symm

/-- A continuous homomorphism from a product to a group with no small subgroups
factors through some finite coordinate restriction, uniquely for that restriction. -/
theorem exists_finset_factor (f : (∀ i, G i) →ₜ* D) [NoSmallSubgroups D] :
    ∃ s : Finset ι, ∃! g : (∀ i : {i // i ∈ s}, G i) →ₜ* D,
      ∀ x : ∀ i, G i, f x = g (fun i => x i) := by
  obtain ⟨s, hs⟩ :=
    f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
  exact ⟨s, f.finiteCoordinateFactor s,
    fun x => (f.finiteCoordinateFactor_restrict s hs x).symm,
    fun g hg => f.finiteCoordinateFactor_unique s g hg⟩

end ContinuousMonoidHom

end Group
