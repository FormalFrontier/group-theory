/-
Copyright (c) 2026 Ember. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.DirectSum

/-!
# Naturality for continuous homomorphisms from discrete direct sums

Restriction to the summands commutes with continuous target postcomposition and
with precomposition by maps of discrete direct sums. The corresponding extension
laws follow from the restriction laws and the inverse identities of
`ContinuousMonoidHom.directSumEquivPi`.

For an arbitrary index map `σ` and coordinate homomorphisms `α`, the source map is
written as the extension of the inclusions at `σ i` composed with `α i`. Each
inclusion is the restriction of the identity on the target direct sum. Colliding
indices and infinite fibres are allowed: inputs to a direct sum have finite support.
The coordinate homomorphisms are expressed on multiplicative tags; discreteness of
the given source topologies makes this equivalent to using all additive monoid
homomorphisms. No joint continuity in the index or coordinate maps is asserted.
-/

@[expose] public section

open scoped DirectSum

universe u v w x y z

section Target

variable {ι : Type u} (A : ι → Type v)
  [∀ i, AddCommMonoid (A i)]
  [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
  [TopologicalSpace (⨁ i, A i)] [DiscreteTopology (⨁ i, A i)]
  {D : Type w} {E : Type z}
  [CommMonoid D] [TopologicalSpace D] [ContinuousMul D]
  [CommMonoid E] [TopologicalSpace E] [ContinuousMul E]

/-- Restriction to the summands commutes with continuous target postcomposition. -/
theorem ContinuousMonoidHom.directSumEquivPi_comp
    (ψ : D →ₜ* E) (f : Multiplicative (⨁ i, A i) →ₜ* D) :
    ContinuousMonoidHom.directSumEquivPi A E (ψ.comp f) =
      fun i => ψ.comp (ContinuousMonoidHom.directSumEquivPi A D f i) := by
  funext i
  ext x
  rfl

/-- Extension from the summands commutes with continuous target postcomposition. -/
theorem ContinuousMonoidHom.comp_directSumEquivPi_symm
    (ψ : D →ₜ* E) (g : ∀ i, Multiplicative (A i) →ₜ* D) :
    ψ.comp ((ContinuousMonoidHom.directSumEquivPi A D).symm g) =
      (ContinuousMonoidHom.directSumEquivPi A E).symm (fun i => ψ.comp (g i)) := by
  apply (ContinuousMonoidHom.directSumEquivPi A E).injective
  rw [ContinuousMonoidHom.directSumEquivPi_comp,
    (ContinuousMonoidHom.directSumEquivPi A D).apply_symm_apply,
    (ContinuousMonoidHom.directSumEquivPi A E).apply_symm_apply]

end Target

section Source

variable {ι : Type u} {κ : Type v} (A : ι → Type w) (B : κ → Type x)
  [∀ i, AddCommMonoid (A i)] [∀ j, AddCommMonoid (B j)]
  [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
  [∀ j, TopologicalSpace (B j)] [∀ j, DiscreteTopology (B j)]
  [TopologicalSpace (⨁ i, A i)] [DiscreteTopology (⨁ i, A i)]
  [TopologicalSpace (⨁ j, B j)] [DiscreteTopology (⨁ j, B j)]
  {D : Type y} [CommMonoid D] [TopologicalSpace D] [ContinuousMul D]

/-- Restriction commutes with the induced map of discrete direct sums for arbitrary
index and coordinate maps. Coordinates are continuous homomorphisms on multiplicative
tags, which for discrete summands represent all additive monoid homomorphisms. -/
theorem ContinuousMonoidHom.directSumEquivPi_comp_induced
    (σ : ι → κ) (α : ∀ i, Multiplicative (A i) →ₜ* Multiplicative (B (σ i)))
    (F : Multiplicative (⨁ j, B j) →ₜ* D) :
    ContinuousMonoidHom.directSumEquivPi A D
      (F.comp
        ((ContinuousMonoidHom.directSumEquivPi A (Multiplicative (⨁ j, B j))).symm
          (fun i =>
            (ContinuousMonoidHom.directSumEquivPi B (Multiplicative (⨁ j, B j))
              (ContinuousMonoidHom.id (Multiplicative (⨁ j, B j))) (σ i)).comp (α i)))) =
      fun i => (ContinuousMonoidHom.directSumEquivPi B D F (σ i)).comp (α i) := by
  rw [ContinuousMonoidHom.directSumEquivPi_comp,
    (ContinuousMonoidHom.directSumEquivPi A (Multiplicative (⨁ j, B j))).apply_symm_apply]
  funext i
  ext a
  rfl

/-- Extension commutes with the induced map of discrete direct sums for arbitrary
index and coordinate maps, expressed on multiplicative tags of discrete summands. -/
theorem ContinuousMonoidHom.directSumEquivPi_symm_comp_induced
    (σ : ι → κ) (α : ∀ i, Multiplicative (A i) →ₜ* Multiplicative (B (σ i)))
    (g : ∀ j, Multiplicative (B j) →ₜ* D) :
    (ContinuousMonoidHom.directSumEquivPi A D).symm (fun i => (g (σ i)).comp (α i)) =
      ((ContinuousMonoidHom.directSumEquivPi B D).symm g).comp
        ((ContinuousMonoidHom.directSumEquivPi A (Multiplicative (⨁ j, B j))).symm
          (fun i =>
            (ContinuousMonoidHom.directSumEquivPi B (Multiplicative (⨁ j, B j))
              (ContinuousMonoidHom.id (Multiplicative (⨁ j, B j))) (σ i)).comp (α i))) := by
  apply (ContinuousMonoidHom.directSumEquivPi A D).injective
  rw [(ContinuousMonoidHom.directSumEquivPi A D).apply_symm_apply,
    ContinuousMonoidHom.directSumEquivPi_comp_induced,
    (ContinuousMonoidHom.directSumEquivPi B D).apply_symm_apply]

end Source
