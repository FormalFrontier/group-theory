/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Additive and multiplicative topology type tags

Continuous additive homomorphisms transport to multiplicative type tags, preserving
identities and composition. Nonarchimedeanness transports in the same direction.

`ContinuousMonoidHom.toAdditiveRight` lifts Mathlib's one-sided algebraic type-tag
equivalence to a homeomorphism for the compact-open topologies. It keeps the original
additive source and needs no continuity of the source or target operations. For a
commutative target with continuous multiplication, `toAdditiveRightContinuousAddEquiv`
also preserves pointwise addition.
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

namespace ContinuousMonoidHom

variable {A : Type u} {B : Type v} [AddMonoid A] [Monoid B]
  [TopologicalSpace A] [TopologicalSpace B]

/-- Reinterpret continuous homomorphisms from a multiplicatively tagged additive monoid
as continuous additive homomorphisms to an additively tagged monoid. Both spaces have
the compact-open topology. This lifts `MonoidHom.toAdditiveRight` and its stock inverse. -/
def toAdditiveRight : (Multiplicative A →ₜ* B) ≃ₜ (A →ₜ+ Additive B) where
  toFun f :=
    { toAddMonoidHom := MonoidHom.toAdditiveRight f.toMonoidHom
      continuous_toFun := continuous_ofMul.comp (f.continuous.comp continuous_ofAdd) }
  invFun f :=
    { toMonoidHom := AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom
      continuous_toFun := continuous_toMul.comp (f.continuous.comp continuous_toAdd) }
  left_inv f := by ext a; rfl
  right_inv f := by ext a; rfl
  continuous_toFun := by
    apply (ContinuousAddMonoidHom.isInducing_toContinuousMap A (Additive B)).continuous_iff.mpr
    exact (ContinuousMap.continuous_postcomp ⟨_, continuous_ofMul⟩).comp
      ((ContinuousMap.continuous_precomp ⟨_, continuous_ofAdd⟩).comp
        (isInducing_toContinuousMap (Multiplicative A) B).continuous)
  continuous_invFun := by
    apply (isInducing_toContinuousMap (Multiplicative A) B).continuous_iff.mpr
    exact (ContinuousMap.continuous_postcomp ⟨_, continuous_toMul⟩).comp
      ((ContinuousMap.continuous_precomp ⟨_, continuous_toAdd⟩).comp
        (ContinuousAddMonoidHom.isInducing_toContinuousMap A (Additive B)).continuous)

@[simp] theorem toAdditiveRight_apply (f : Multiplicative A →ₜ* B) (a : A) :
    toAdditiveRight f a = Additive.ofMul (f (Multiplicative.ofAdd a)) := rfl

@[simp] theorem toAdditiveRight_symm_apply (f : A →ₜ+ Additive B) (a : Multiplicative A) :
    toAdditiveRight.symm f a = Additive.toMul (f a.toAdd) := rfl

/-- Forgetting continuity recovers Mathlib's one-sided algebraic equivalence. -/
theorem toAdditiveRight_toAddMonoidHom (f : Multiplicative A →ₜ* B) :
    (toAdditiveRight f).toAddMonoidHom = MonoidHom.toAdditiveRight f.toMonoidHom := rfl

/-- The inverse likewise uses Mathlib's conversion on the original additive source. -/
theorem toAdditiveRight_symm_toMonoidHom (f : A →ₜ+ Additive B) :
    (toAdditiveRight.symm f).toMonoidHom =
      AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom := rfl

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {A : Type u} {B : Type v} [AddMonoid A] [CommMonoid B]
  [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul B]

/-- The one-sided type-tag homeomorphism preserves pointwise addition when the target
is a commutative monoid with continuous multiplication. The underlying algebraic
conversion is `MonoidHom.toAdditiveRightMulEquiv`. -/
def toAdditiveRightContinuousAddEquiv :
    Additive (Multiplicative A →ₜ* B) ≃ₜ+ (A →ₜ+ Additive B) where
  toFun f := toAdditiveRight f.toMul
  invFun f := Additive.ofMul (toAdditiveRight.symm f)
  left_inv f := by
    exact congrArg Additive.ofMul (toAdditiveRight.symm_apply_apply f.toMul)
  right_inv f := toAdditiveRight.apply_symm_apply f
  map_add' f g := by
    apply ContinuousAddMonoidHom.ext
    intro a
    exact congrArg (fun h : Multiplicative (A →+ Additive B) => h.toAdd a)
      (MonoidHom.toAdditiveRightMulEquiv.map_mul f.toMul.toMonoidHom g.toMul.toMonoidHom)
  continuous_toFun := toAdditiveRight.continuous.comp continuous_toMul
  continuous_invFun := continuous_ofMul.comp toAdditiveRight.symm.continuous

@[simp] theorem toAdditiveRightContinuousAddEquiv_apply
    (f : Additive (Multiplicative A →ₜ* B)) :
    toAdditiveRightContinuousAddEquiv f = toAdditiveRight f.toMul := rfl

@[simp] theorem toAdditiveRightContinuousAddEquiv_symm_apply (f : A →ₜ+ Additive B) :
    toAdditiveRightContinuousAddEquiv.symm f = Additive.ofMul (toAdditiveRight.symm f) := rfl

end ContinuousMonoidHom

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
