/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.UnitsNeighborhood
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Hom
import GroupTheory.Topology.ValueSubgroups

/-!
# Finite-coordinate factorization from a neighborhood of the identity

A family of homomorphisms from a product of groups kills one common coordinate
tail if a common identity neighborhood maps into a set containing the values of
no nontrivial subgroup of the target's units. The target is an arbitrary monoid;
no topology on it is needed for this criterion.

If the target has a topology and its units have no small subgroups, common
control of identity neighborhoods gives the same conclusion. In particular, a
continuous homomorphism factors through finitely many coordinates whenever an
open identity neighborhood contains the values of no nontrivial subgroup of
units. Neither source nor target multiplication is required to be continuous,
and no separation assumption is used.

The proof sends the entire subgroup of tuples equal to one on a finite set of
coordinates into the canonical group of units, then applies the canonical
finite-coordinate factorization criterion.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition.
-/

@[expose] public section

open Filter Topology

universe z u v w

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

/-- If all members of a family send one common identity neighborhood into a set
containing the values of no nontrivial subgroup of units, they kill one common
coordinate tail in the canonical group of units. The whole tail subgroup is
killed, not just its finitely supported elements. No topology on the target
monoid or nonemptiness of the family is required. -/
theorem exists_finset_forall_coordinateKernel_le_ker_toHomUnits_of_subgroup_values
    {A : Type z} {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [Monoid D]
    (F : A → ((∀ i, G i) →* D))
    (U : Set (∀ i, G i)) (hU : U ∈ 𝓝 (1 : ∀ i, G i))
    (V : Set D) (hF : ∀ a, Set.MapsTo (F a) U V)
    (hsub : ∀ H : Subgroup Dˣ, (∀ z ∈ H, (z : D) ∈ V) → H = ⊥) :
    ∃ s : Finset ι, ∀ a,
      Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤
        (F a).toHomUnits.ker := by
  classical
  have h1U : (1 : ∀ i, G i) ∈ U := mem_of_mem_nhds hU
  rw [nhds_pi] at hU
  obtain ⟨s, hs, W, hW, hWU⟩ := Filter.mem_pi.mp hU
  let K : Subgroup (∀ i, G i) :=
    Subgroup.pi s (fun i => (⊥ : Subgroup (G i)))
  have hkill (a : A) : ∀ x ∈ K, F a x = 1 := by
    have h1 : (1 : D) ∈ V := by
      simpa only [map_one] using hF a h1U
    have hmaps : Set.MapsTo (F a) (K : Set (∀ i, G i)) V := by
      intro x hx
      apply hF a
      apply hWU
      intro i hi
      have hxi : x i = 1 := hx i hi
      rw [hxi]
      exact mem_of_mem_nhds (hW i)
    have hiff : Set.MapsTo (F a) (K : Set (∀ i, G i)) V ↔
        ∀ x ∈ K, F a x = 1 := by
      apply MonoidHom.mapsTo_iff_eq_one_of_subgroup_values
        (f := F a) (H := K) (V := V)
      all_goals assumption
    exact hiff.mp hmaps
  refine ⟨hs.toFinset, fun a x hx => MonoidHom.mem_ker.mpr ?_⟩
  apply Units.ext
  change F a x = 1
  apply hkill a
  intro i hi
  exact hx i (by simpa using hi)

/-- Common control of identity neighborhoods for a family of homomorphisms into
a monoid with a given topology whose units have no small subgroups forces one
common coordinate tail into every canonical units kernel. No continuity of
operations or compatibility of the topology with multiplication is assumed. -/
theorem exists_finset_forall_coordinateKernel_le_ker_toHomUnits
    {A : Type z} {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D] [NoSmallSubgroups Dˣ]
    (F : A → ((∀ i, G i) →* D))
    (hF : ∀ W : Set D, W ∈ 𝓝 (1 : D) →
      ∃ U : Set (∀ i, G i), U ∈ 𝓝 (1 : ∀ i, G i) ∧
        ∀ a, Set.MapsTo (F a) U W) :
    ∃ s : Finset ι, ∀ a,
      Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤
        (F a).toHomUnits.ker := by
  obtain ⟨V, hV, h1, hsub⟩ :=
    Units.noSmallSubgroups_iff_exists_open_subgroup_eq_bot.mp
      (inferInstance : NoSmallSubgroups Dˣ)
  obtain ⟨U, hU, hUV⟩ := hF V (hV.mem_nhds h1)
  exact exists_finset_forall_coordinateKernel_le_ker_toHomUnits_of_subgroup_values
    F U hU V hUV hsub

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
  obtain ⟨s, hs⟩ :=
    MonoidHom.exists_finset_forall_coordinateKernel_le_ker_toHomUnits_of_subgroup_values
      (fun _ : Unit => f.toMonoidHom)
      ((f : (∀ i, G i) → D) ⁻¹' V) hpre V (fun _ _ hx => hx) hsub
  refine ⟨s, (f.eq_finiteCoordinateFactor_comp_restrict_iff_eq_one s).2 ?_⟩
  intro x hx
  have hxK : x ∈ Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) := by
    intro i hi
    exact hx i hi
  have hxunit : f.toMonoidHom.toHomUnits x = 1 :=
    MonoidHom.mem_ker.mp (hs () hxK)
  exact congrArg (fun z : Dˣ => (z : D)) hxunit

end ContinuousMonoidHom
