/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Constructions

/-!
# Continuous homomorphisms into compatible sections

The existing sections subtype of a monoid-valued functor has continuous coordinate
projections and a coordinatewise lift of compatible continuous homomorphisms.
Neither the transition maps nor multiplication on the stages need be continuous.

The same API applies to group-valued functors through the forgetful functor to monoids.
Unlike inverse systems indexed by a filtered category, the construction allows any
category, including empty categories and parallel arrows.
-/

@[expose] public section

open CategoryTheory

universe u u' v w

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})
variable [stageTopologies : ∀ j : J, TopologicalSpace (F.obj j)]

local instance : ∀ j : J, TopologicalSpace ((F ⋙ forget MonCat).obj j) :=
  fun j => stageTopologies j

/-- The continuous coordinate projection from compatible monoid sections. -/
def sectionsπContinuousMonoidHom (j : J) :
    (F ⋙ forget MonCat).sections →ₜ* F.obj j where
  toFun s := s.val j
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_apply j).comp continuous_subtype_val

@[simp]
theorem sectionsπContinuousMonoidHom_apply (j : J)
    (s : (F ⋙ forget MonCat).sections) :
    sectionsπContinuousMonoidHom F j s = s.val j := rfl

/-- The coordinate projections respect every arrow, including parallel arrows. -/
theorem sectionsπContinuousMonoidHom_naturality {i j : J} (f : i ⟶ j)
    (s : (F ⋙ forget MonCat).sections) :
    F.map f (sectionsπContinuousMonoidHom F i s) =
      sectionsπContinuousMonoidHom F j s :=
  s.property f

variable {H : Type u'} [Monoid H] [TopologicalSpace H]

/-- Lift a compatible family of continuous homomorphisms to compatible sections. -/
def sectionsLift (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x) :
    H →ₜ* (F ⋙ forget MonCat).sections where
  toFun x := ⟨fun j => q j x, fun f => hq f x⟩
  map_one' := by
    apply Subtype.ext
    funext j
    exact (q j).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext j
    exact (q j).map_mul x y
  continuous_toFun :=
    Continuous.subtype_mk (continuous_pi (fun j => (q j).continuous))
      (fun x {i j} f => hq f x)

@[simp]
theorem sectionsπ_sectionsLift_apply (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x)
    (j : J) (x : H) :
    sectionsπContinuousMonoidHom F j (sectionsLift F q hq x) = q j x := rfl

/-- Projecting a lifted family recovers its specified continuous homomorphism. -/
theorem sectionsπ_comp_sectionsLift (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x)
    (j : J) :
    (sectionsπContinuousMonoidHom F j).comp (sectionsLift F q hq) = q j := by
  ext x
  exact sectionsπ_sectionsLift_apply F q hq j x

/-- A continuous sections homomorphism is determined by its projections. -/
theorem sectionsLift_unique (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x)
    (g : H →ₜ* (F ⋙ forget MonCat).sections)
    (hg : ∀ j, (sectionsπContinuousMonoidHom F j).comp g = q j) :
    g = sectionsLift F q hq := by
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  funext j
  have hj := congrArg (fun f : H →ₜ* F.obj j => f x) (hg j)
  exact hj

/-- Precomposing a sections lift precomposes every component. -/
theorem sectionsLift_comp {K : Type*} [Monoid K] [TopologicalSpace K]
    (q : ∀ j : J, H →ₜ* F.obj j)
    (hq : ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x)
    (g : K →ₜ* H) :
    sectionsLift F (fun j => (q j).comp g)
      (by intro i j f x; exact hq f (g x)) = (sectionsLift F q hq).comp g := by
  apply ContinuousMonoidHom.ext
  intro x
  apply Subtype.ext
  funext j
  rfl

/-- Continuous homomorphisms to sections are equivalent to compatible families of
continuous homomorphisms into the stages. -/
def sectionsHomEquiv :
    (H →ₜ* (F ⋙ forget MonCat).sections) ≃
      { q : ∀ j : J, H →ₜ* F.obj j //
        ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x } where
  toFun g := ⟨fun j => (sectionsπContinuousMonoidHom F j).comp g,
    fun f x => sectionsπContinuousMonoidHom_naturality F f (g x)⟩
  invFun q := sectionsLift F q.val q.property
  left_inv := by
    intro g
    exact (sectionsLift_unique F (fun j => (sectionsπContinuousMonoidHom F j).comp g)
      (fun f x => sectionsπContinuousMonoidHom_naturality F f (g x)) g
      (fun _ => rfl)).symm
  right_inv := by
    intro q
    apply Subtype.ext
    funext j
    exact sectionsπ_comp_sectionsLift F q.val q.property j

@[simp]
theorem sectionsHomEquiv_apply_apply (g : H →ₜ* (F ⋙ forget MonCat).sections)
    (j : J) (x : H) : (sectionsHomEquiv F g).val j x = (g x).val j := by
  rfl

@[simp]
theorem sectionsHomEquiv_symm_apply_apply
    (q : { q : ∀ j : J, H →ₜ* F.obj j //
      ∀ {i j : J} (f : i ⟶ j) (x : H), F.map f (q i x) = q j x })
    (j : J) (x : H) :
    sectionsπContinuousMonoidHom F j ((sectionsHomEquiv F).symm q x) = q.val j x := by
  rfl

/-- The sections topology is induced by all its coordinate projections. -/
theorem sections_topology :
    (inferInstance : TopologicalSpace (F ⋙ forget MonCat).sections) =
      ⨅ j : J, TopologicalSpace.induced
        (fun s : (F ⋙ forget MonCat).sections => s.val j)
        (inferInstance : TopologicalSpace (F.obj j)) := by
  exact induced_to_pi
    (fun s : (F ⋙ forget MonCat).sections => s.val)

end MonCat

namespace GrpCat

variable {J : Type v} [Category.{w} J] (G : J ⥤ GrpCat.{u})
variable [stageTopologies : ∀ j : J, TopologicalSpace (G.obj j)]

local instance : ∀ j : J, TopologicalSpace ((G ⋙ forget GrpCat).obj j) :=
  fun j => stageTopologies j

/-- Continuous coordinate projection for group-valued sections, extending the
existing algebraic projection. -/
def sectionsπContinuousMonoidHom (j : J) :
    (G ⋙ forget GrpCat).sections →ₜ* G.obj j where
  toMonoidHom := sectionsπMonoidHom G j
  continuous_toFun := (continuous_apply j).comp continuous_subtype_val

@[simp]
theorem sectionsπContinuousMonoidHom_apply (j : J)
    (s : (G ⋙ forget GrpCat).sections) :
    sectionsπContinuousMonoidHom G j s = s.val j := rfl

/-- Forgetting continuity recovers the algebraic sections projection. -/
theorem sectionsπContinuousMonoidHom_toMonoidHom (j : J) :
    (sectionsπContinuousMonoidHom G j).toMonoidHom = sectionsπMonoidHom G j := rfl

end GrpCat
