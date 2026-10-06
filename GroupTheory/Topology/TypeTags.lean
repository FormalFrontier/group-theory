/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Additive and multiplicative topology type tags

Continuous additive homomorphisms transport to multiplicative type tags, preserving
identities and composition. Nonarchimedeanness transports in the same direction.
-/

@[expose] public section

open Filter
open scoped Topology

universe u v w

namespace ContinuousAddMonoidHom

variable {A : Type u} {B : Type v} {C : Type w}
  [AddMonoid A] [AddMonoid B] [AddMonoid C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- A continuous additive homomorphism, expressed between multiplicative type tags. -/
def toMultiplicative (f : A →ₜ+ B) : Multiplicative A →ₜ* Multiplicative B where
  toMonoidHom := f.toAddMonoidHom.toMultiplicative
  continuous_toFun := f.continuous

@[simp] theorem toMultiplicative_apply (f : A →ₜ+ B) (a : A) :
    toMultiplicative f (Multiplicative.ofAdd a) = Multiplicative.ofAdd (f a) := rfl

/-- Type-tag transport takes the identity to the identity. -/
@[simp] theorem toMultiplicative_id :
    (ContinuousAddMonoidHom.id A).toMultiplicative =
      ContinuousMonoidHom.id (Multiplicative A) := by
  ext a
  rfl

/-- Type-tag transport respects composition of continuous additive homomorphisms. -/
@[simp] theorem toMultiplicative_comp (g : B →ₜ+ C) (f : A →ₜ+ B) :
    (g.comp f).toMultiplicative = g.toMultiplicative.comp f.toMultiplicative := by
  ext a
  rfl

end ContinuousAddMonoidHom

namespace NonarchimedeanAddGroup

variable {A : Type u} [AddGroup A] [TopologicalSpace A] [NonarchimedeanAddGroup A]

/-- Nonarchimedeanness is unchanged by the multiplicative type tag. -/
instance instMultiplicative : NonarchimedeanGroup (Multiplicative A) where
  is_nonarchimedean U hU := by
    have hU' : (U : Set A) ∈ 𝓝 (0 : A) := by
      change (U : Set A) ∈ 𝓝 ((1 : Multiplicative A).toAdd)
      rw [nhds_toAdd]
      exact hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean
      (G := A) (U : Set A) hU'
    exact ⟨⟨AddSubgroup.toSubgroup V.toAddSubgroup, V.isOpen⟩, hV⟩

end NonarchimedeanAddGroup

end
