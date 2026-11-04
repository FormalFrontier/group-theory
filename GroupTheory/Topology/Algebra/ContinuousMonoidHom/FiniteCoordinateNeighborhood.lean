/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Finite-coordinate factorization from a neighborhood of the identity

A continuous homomorphism from a product of groups factors through finitely many
coordinates if an open identity neighborhood in its target contains the values
of no nontrivial subgroup of the target's units. Neither source nor target
multiplication is required to be continuous, and no separation assumption is used.

The proof sends the entire subgroup of tuples equal to one on a finite set of
coordinates into the canonical group of units, then applies the canonical
finite-coordinate factorization criterion.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition.
-/

@[expose] public section

open Filter Topology

universe u v w

namespace MonoidHom

/-- Equality with the fixed finite-coordinate factor is equivalent to sending every
point of the complementary coordinate tail to the identity. -/
theorem eq_finiteCoordinateFactor_comp_restrict_iff_eq_one
    {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, MulOneClass (G i)] [MulOneClass D]
    (f : (∀ i, G i) →* D) (s : Finset ι) :
    ((f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i)) ↔
      ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 := by
  constructor
  · intro h x hx
    have hrestrict : (fun i : {i // i ∈ s} => x i) = 1 := by
      funext i
      exact hx i i.property
    calc
      f x = f.finiteCoordinateFactor s (fun i => x i) := congrFun h x
      _ = f.finiteCoordinateFactor s 1 := congrArg _ hrestrict
      _ = 1 := map_one _
  · exact f.eq_finiteCoordinateFactor_comp_restrict_of_eq_one s

end MonoidHom

namespace ContinuousMonoidHom

/-- Equality with the fixed continuous finite-coordinate factor is equivalent to
sending every point of the complementary coordinate tail to the identity. -/
theorem eq_finiteCoordinateFactor_comp_restrict_iff_eq_one
    {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]
    (f : (∀ i, G i) →ₜ* D) (s : Finset ι) :
    ((f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i)) ↔
      ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 :=
  f.toMonoidHom.eq_finiteCoordinateFactor_comp_restrict_iff_eq_one s

variable {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- An open identity neighborhood containing the values of no nontrivial subgroup
of the target's units forces a continuous homomorphism from a product of groups
to equal its canonical finite-coordinate factor after coordinate restriction. -/
theorem exists_eq_finiteCoordinateFactor_comp_restrict_of_subgroup_values
    (f : (∀ i, G i) →ₜ* D) (V : Set D) (hV : IsOpen V) (h1 : (1 : D) ∈ V)
    (hsub : ∀ H : Subgroup Dˣ, (∀ z ∈ H, (z : D) ∈ V) → H = ⊥) :
    ∃ s : Finset ι, (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  classical
  have hpre : (f : (∀ i, G i) → D) ⁻¹' V ∈ 𝓝 (1 : ∀ i, G i) :=
    (hV.preimage f.continuous).mem_nhds (by simpa using h1)
  rw [nhds_pi] at hpre
  obtain ⟨s, hs, U, hU, hUV⟩ := Filter.mem_pi.mp hpre
  let K : Subgroup (∀ i, G i) :=
    Subgroup.pi s (fun i => (⊥ : Subgroup (G i)))
  have hmap : K.map f.toMonoidHom.toHomUnits = ⊥ := by
    apply hsub
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    change f x ∈ V
    apply hUV
    intro i hi
    have hxi : x i = 1 := hx i hi
    rw [hxi]
    exact mem_of_mem_nhds (hU i)
  refine ⟨hs.toFinset,
    (f.eq_finiteCoordinateFactor_comp_restrict_iff_eq_one hs.toFinset).2 ?_⟩
  intro x hx
  have hxK : x ∈ K := by
    intro i hi
    exact hx i (by simpa using hi)
  have hxmap : f.toMonoidHom.toHomUnits x ∈ K.map f.toMonoidHom.toHomUnits :=
    ⟨x, hxK, rfl⟩
  rw [hmap] at hxmap
  have hxunit : f.toMonoidHom.toHomUnits x = 1 := hxmap
  exact congrArg (fun z : Dˣ => (z : D)) hxunit

end ContinuousMonoidHom
