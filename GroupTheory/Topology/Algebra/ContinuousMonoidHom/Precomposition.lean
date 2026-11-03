/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import Mathlib.Topology.Maps.Basic

/-!
# Split precomposition on continuous monoid homomorphisms

Precomposition by a continuous monoid homomorphism with a continuous right inverse
embeds compact-open homomorphism spaces. In particular, restriction to any finite
set of coordinates gives an embedding from a finite-product homomorphism space
into the full-product homomorphism space.

The finite-coordinate case uses extension by the identity through
`ContinuousMonoidHom.finiteCoordinateFactor`.
-/

@[expose] public section

universe u v w

namespace ContinuousMonoidHom

section Split

variable {A : Type u} {B : Type v} {D : Type w}
variable [Monoid A] [Monoid B] [Monoid D]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]

/-- Precomposition by a continuous monoid homomorphism with a continuous right
inverse is an embedding for the compact-open topologies. -/
theorem isEmbedding_comp_left (r : A →ₜ* B) (e : B →ₜ* A)
    (h : Function.RightInverse e r) :
    Topology.IsEmbedding (fun f : B →ₜ* D => f.comp r) := by
  have hleft : Function.LeftInverse
      (fun g : A →ₜ* D => g.comp e) (fun f : B →ₜ* D => f.comp r) := by
    intro f
    apply ContinuousMonoidHom.ext
    intro b
    exact congrArg f (h b)
  exact Function.LeftInverse.isEmbedding hleft
    (continuous_comp_left e) (continuous_comp_left r)

end Split

section FiniteCoordinates

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
variable [Monoid D] [TopologicalSpace D]

/-- Precomposition by restriction to a finite set of coordinates embeds the
finite-product homomorphism space into the full-product homomorphism space,
with their compact-open topologies. -/
theorem isEmbedding_comp_finiteCoordinateRestriction (s : Finset ι) :
    Topology.IsEmbedding (fun f : (∀ i : {i // i ∈ s}, G i) →ₜ* D =>
      f.comp
        { toFun := fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          continuous_toFun :=
            continuous_pi (fun i : {i // i ∈ s} => continuous_apply (i : ι)) }) := by
  classical
  apply isEmbedding_comp_left _
    ((ContinuousMonoidHom.id (∀ i, G i)).finiteCoordinateFactor s)
  intro x
  funext i
  rw [finiteCoordinateFactor_apply, coe_id]
  change (if hi : (i : ι) ∈ s then x ⟨i, hi⟩ else 1) = x i
  rw [dite_eq_left i.property]

end FiniteCoordinates

end ContinuousMonoidHom
