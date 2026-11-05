/-
Copyright (c) 2026 Ember. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ember
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.DirectSum

/-!
# Target naturality for continuous homomorphisms from discrete direct sums

Restriction to the summands commutes with continuous target postcomposition.
The corresponding extension law follows from this restriction law and the inverse
identities of `ContinuousMonoidHom.directSumEquivPi`.
-/

@[expose] public section

open scoped DirectSum

universe u v w z

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
