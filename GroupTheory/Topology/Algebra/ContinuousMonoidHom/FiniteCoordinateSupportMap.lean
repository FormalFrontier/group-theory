/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateSupport

/-!
# Coordinate support and reconstruction under postcomposition

Postcomposition sends each coordinate homomorphism to its composite and can only
remove coordinates from the support. A homomorphism that reflects the identity
preserves coordinate support. These facts transport a common finite coordinate
support for an arbitrary family, without a finiteness assumption on the family.

Injective homomorphisms reflect pointwise reconstruction by the canonical finite
factor. For reconstruction at every input, reflection of the identity suffices:
apply reconstruction to inputs equal to one on the chosen coordinates, then use
the existing whole-tail reconstruction theorem. Only the unit laws are required;
no associativity or topological assumptions are used.

Coordinate support alone does not assert reconstruction of an arbitrary
homomorphism from an infinite product.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable

universe u v w z t

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w} {E : Type z}
  [∀ i, MulOneClass (G i)] [MulOneClass D] [MulOneClass E]

/-- Restricting a postcomposition to one coordinate commutes with composition. -/
@[simp]
theorem coordinateHom_comp (f : (∀ i, G i) →* D) (h : D →* E) (i : ι) :
    (h.comp f).coordinateHom i = h.comp (f.coordinateHom i) := by
  ext a
  simp only [coordinateHom_apply, comp_apply]

/-- Postcomposition can only remove coordinates from coordinate support. -/
theorem coordinateMulSupport_comp_subset (f : (∀ i, G i) →* D) (h : D →* E) :
    (h.comp f).coordinateMulSupport ⊆ f.coordinateMulSupport := by
  apply (coordinateMulSupport_subset_iff_coordinate_values_eq_one _ _).2
  intro i hi a
  have ha := (not_mem_coordinateMulSupport_iff f i).1 hi a
  simp only [coordinateHom_comp, comp_apply, ha, map_one]

/-- A homomorphism that reflects the identity preserves coordinate support. -/
theorem coordinateMulSupport_comp_eq_of_reflects_one
    (f : (∀ i, G i) →* D) (h : D →* E) (h1 : ∀ d, h d = 1 → d = 1) :
    (h.comp f).coordinateMulSupport = f.coordinateMulSupport := by
  refine Set.Subset.antisymm (coordinateMulSupport_comp_subset f h) ?_
  intro i hi
  obtain ⟨a, ha⟩ := (mem_coordinateMulSupport_iff f i).1 hi
  refine (mem_coordinateMulSupport_iff (h.comp f) i).2 ⟨a, ?_⟩
  intro hval
  apply ha
  apply h1
  simpa only [coordinateHom_comp, comp_apply] using hval

/-- Injective postcomposition preserves coordinate support. -/
theorem coordinateMulSupport_comp_eq_of_injective
    (f : (∀ i, G i) →* D) (h : D →* E) (hinj : Function.Injective h) :
    (h.comp f).coordinateMulSupport = f.coordinateMulSupport :=
  coordinateMulSupport_comp_eq_of_reflects_one f h
    (fun _ hd => hinj (hd.trans h.map_one.symm))

section Family

variable {A : Type t}

/-- Postcomposition transports a common finite coordinate support for any family. -/
theorem finite_iUnion_coordinateMulSupport_comp
    (f : A → (∀ i, G i) →* D) (h : D →* E)
    (hf : (⋃ a, (f a).coordinateMulSupport).Finite) :
    (⋃ a, (h.comp (f a)).coordinateMulSupport).Finite :=
  hf.subset (Set.iUnion_mono fun a => coordinateMulSupport_comp_subset (f a) h)

/-- Identity-reflecting postcomposition preserves the existence of a common finite
coordinate support, even for an infinite family. -/
theorem finite_iUnion_coordinateMulSupport_comp_iff_of_reflects_one
    (f : A → (∀ i, G i) →* D) (h : D →* E) (h1 : ∀ d, h d = 1 → d = 1) :
    (⋃ a, (h.comp (f a)).coordinateMulSupport).Finite ↔
      (⋃ a, (f a).coordinateMulSupport).Finite := by
  simp only [coordinateMulSupport_comp_eq_of_reflects_one _ h h1]

end Family

/-- An injective postcomposition reflects reconstruction at any fixed input by
the canonical finite-coordinate factor. -/
theorem finiteCoordinateFactor_comp_apply_eq_iff
    (f : (∀ i, G i) →* D) (h : D →* E) (hinj : Function.Injective h)
    (s : Finset ι) (x : ∀ i, G i) :
    (h.comp f).finiteCoordinateFactor s (fun i => x i) = (h.comp f) x ↔
      f.finiteCoordinateFactor s (fun i => x i) = f x := by
  simp only [finiteCoordinateFactor_comp, comp_apply]
  constructor
  · intro hx
    exact hinj hx
  · intro hx
    exact congrArg h hx

/-- Postcomposition by a homomorphism that reflects the identity preserves and
reflects reconstruction at every input by a fixed canonical finite factor.
Unlike reflection at just one input, injectivity is not required. -/
theorem finiteCoordinateFactor_comp_restrict_eq_iff
    (f : (∀ i, G i) →* D) (h : D →* E)
    (hone : ∀ d, h d = 1 → d = 1) (s : Finset ι) :
    (∀ x : ∀ i, G i,
      (h.comp f).finiteCoordinateFactor s (fun i => x i) = (h.comp f) x) ↔
      ∀ x : ∀ i, G i, f.finiteCoordinateFactor s (fun i => x i) = f x := by
  constructor
  · intro hrec
    have hs : ∀ y : ∀ i, G i, (∀ i ∈ s, y i = 1) → f y = 1 := by
      intro y hy
      apply hone
      have hrestrict : (fun i : {i // i ∈ s} => y i) = 1 := by
        funext i
        exact hy i i.property
      have hyrec := hrec y
      rw [hrestrict, map_one, comp_apply] at hyrec
      exact hyrec.symm
    intro x
    exact f.finiteCoordinateFactor_restrict_of_eq_one s hs x
  · intro hrec x
    simpa only [finiteCoordinateFactor_comp, comp_apply] using congrArg h (hrec x)

end MonoidHom
