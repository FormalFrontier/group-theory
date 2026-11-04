/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateCompact
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Precomposition

/-!
# Compact subsets of finite-coordinate homomorphism spaces

A compact family of continuous homomorphisms from a product of groups to a monoid
whose unit group has no small subgroups is the image of a compact family on one
finite subproduct, under precomposition with coordinate restriction.
-/

@[expose] public section

namespace ContinuousMonoidHom

/-- A family of continuous homomorphisms is compact if and only if it is the image
of a compact family on one finite subproduct under coordinate restriction. -/
theorem isCompact_iff_exists_comp_restrict_image
    {ι : Type*} {G : ι → Type*} {D : Type*}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D] [NoSmallSubgroups Dˣ]
    {K : Set ((∀ i, G i) →ₜ* D)} :
    IsCompact K ↔ ∃ (s : Finset ι)
      (L : Set (((i : s) → G i) →ₜ* D)), IsCompact L ∧
      K = (fun g => g.comp
        ({ toFun := fun x i => x i
           map_one' := rfl
           map_mul' := fun _ _ => rfl
           continuous_toFun := by fun_prop } :
          (∀ i, G i) →ₜ* ((i : s) → G i))) '' L
    := by
  constructor
  · intro hK
    obtain ⟨s, hs⟩ :=
      exists_eq_finiteCoordinateFactor_comp_restrict_of_isCompact_of_noSmallSubgroups_units K hK
    refine ⟨s, (fun f => f.finiteCoordinateFactor s) '' K, ?_, ?_⟩
    · apply hK.image
      change Continuous (fun f : (∀ i, G i) →ₜ* D =>
        f.comp ((ContinuousMonoidHom.id (∀ i, G i)).finiteCoordinateFactor s))
      exact continuous_comp_left _
    · let p : (∀ i, G i) →ₜ* ((i : s) → G i) :=
        { toFun := fun x i => x i
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          continuous_toFun := by fun_prop }
      have heq : Set.EqOn
          (fun f : (∀ i, G i) →ₜ* D => (f.finiteCoordinateFactor s).comp p) _root_.id K := by
        intro f hf
        ext x
        exact (congrFun (hs f hf) x).symm
      simpa only [Set.image_image, Set.image_id] using heq.image_eq.symm
  · rintro ⟨s, L, hL, rfl⟩
    exact hL.image (continuous_comp_left _)

end ContinuousMonoidHom
