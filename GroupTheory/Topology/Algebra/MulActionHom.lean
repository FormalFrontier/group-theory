/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Topology.CompactOpen

/-!
# Continuous equivariant maps

`ContinuousMulActionHom φ X Y` consists of the `φ`-equivariant maps from `X` to `Y`
that are continuous. The scalar map `φ : M → N` is an arbitrary function, and the
scalar operations on `X` and `Y` need only be `SMul` instances. Neither scalar type
needs a topology or a monoid structure.

The topology is induced by the inclusion into `C(X, Y)` with its compact-open
topology. In particular, evaluation at each fixed point is continuous, without
local compactness of `X` or separation of `Y`.

## Implementation notes

The underlying equivariant map is Mathlib's `MulActionHom`. The two forgetful
interfaces are `MulActionSemiHomClass` and `ContinuousMapClass`. The topology is
not defined using the pointwise topology on `X → Y`.

## References

* Mathlib's equivariant-map API by Kenny Lau and Antoine Chambert-Loir.
* Mathlib's continuous-map API by Nicolò Cavalleri and Yury Kudryashov, and
  Reid Barton's compact-open topology and its fixed-evaluation API.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

/-- A continuous map compatible with scalar operations along an arbitrary function
`φ : M → N`. No action laws or continuity of the scalar operations are required. -/
structure ContinuousMulActionHom {M : Type u₁} {N : Type u₂} (φ : M → N)
    (X : Type v₁) (Y : Type v₂) [SMul M X] [SMul N Y]
    [TopologicalSpace X] [TopologicalSpace Y] extends MulActionHom φ X Y where
  /-- Continuity of the underlying function. -/
  continuous_toFun : Continuous toFun

namespace ContinuousMulActionHom

variable {M : Type u₁} {N : Type u₂} {P : Type u₃}
variable {φ : M → N} {ψ : N → P} {χ : M → P}
variable {X : Type v₁} {Y : Type v₂} {Z : Type v₃}
variable [SMul M X] [SMul N Y] [SMul P Z]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

instance : FunLike (ContinuousMulActionHom φ X Y) X Y where
  coe f := f.toMulActionHom
  coe_injective f g h := by
    cases f with
    | mk f hf =>
      cases g with
      | mk g hg =>
        have hfg : f = g := DFunLike.coe_injective h
        cases hfg
        rfl

instance : MulActionSemiHomClass (ContinuousMulActionHom φ X Y) φ X Y where
  map_smulₛₗ f := f.toMulActionHom.map_smul'

instance : ContinuousMapClass (ContinuousMulActionHom φ X Y) X Y where
  map_continuous f := f.continuous_toFun

/-- Forget equivariance, retaining the continuous map. -/
def toContinuousMap (f : ContinuousMulActionHom φ X Y) : C(X, Y) :=
  ⟨f, f.continuous_toFun⟩

/-- Bundle an equivariant map together with its continuity proof. -/
def ofMulActionHom (f : MulActionHom φ X Y) (hf : Continuous f) :
    ContinuousMulActionHom φ X Y :=
  ⟨f, hf⟩

/-- Bundle a continuous map together with its equivariance proof. -/
def ofContinuousMap (f : C(X, Y))
    (hf : ∀ (m : M) (x : X), f (m • x) = φ m • f x) :
    ContinuousMulActionHom φ X Y :=
  ⟨⟨f, hf⟩, map_continuous f⟩

/-- Bundle a map using the existing continuity and equivariance interfaces. -/
def ofClass {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y]
    [MulActionSemiHomClass F φ X Y] (f : F) : ContinuousMulActionHom φ X Y :=
  ofMulActionHom (MulActionSemiHomClass.toMulActionHom f) (map_continuous f)

/-- Continuous equivariant maps are equal if they agree at every point. -/
@[ext]
theorem ext {f g : ContinuousMulActionHom φ X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Forgetting continuity is injective. -/
theorem toMulActionHom_injective :
    Function.Injective (toMulActionHom : ContinuousMulActionHom φ X Y → MulActionHom φ X Y) := by
  intro f g h
  exact ext fun x => DFunLike.congr_fun h x

/-- Forgetting equivariance is injective. -/
theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : ContinuousMulActionHom φ X Y → C(X, Y)) := by
  intro f g h
  exact ext fun x => DFunLike.congr_fun h x

@[simp]
theorem toMulActionHom_apply (f : ContinuousMulActionHom φ X Y) (x : X) :
    f.toMulActionHom x = f x := rfl

@[simp]
theorem toContinuousMap_apply (f : ContinuousMulActionHom φ X Y) (x : X) :
    f.toContinuousMap x = f x := rfl

@[simp]
theorem coe_toMulActionHom (f : ContinuousMulActionHom φ X Y) :
    ⇑f.toMulActionHom = f := rfl

@[simp]
theorem coe_toContinuousMap (f : ContinuousMulActionHom φ X Y) :
    ⇑f.toContinuousMap = f := rfl

/-- The class-based coercion to equivariant maps is the underlying projection. -/
@[simp]
theorem coe_mulActionHom (f : ContinuousMulActionHom φ X Y) :
    (f : MulActionHom φ X Y) = f.toMulActionHom := rfl

/-- The class-based coercion to continuous maps is the forgetful map. -/
@[simp]
theorem coe_continuousMap (f : ContinuousMulActionHom φ X Y) :
    (f : C(X, Y)) = f.toContinuousMap := rfl

@[simp]
theorem ofMulActionHom_apply (f : MulActionHom φ X Y) (hf : Continuous f) (x : X) :
    ofMulActionHom f hf x = f x := rfl

@[simp]
theorem toMulActionHom_ofMulActionHom (f : MulActionHom φ X Y) (hf : Continuous f) :
    (ofMulActionHom f hf).toMulActionHom = f := rfl

@[simp]
theorem ofContinuousMap_apply (f : C(X, Y))
    (hf : ∀ (m : M) (x : X), f (m • x) = φ m • f x) (x : X) :
    ofContinuousMap f hf x = f x := rfl

@[simp]
theorem toContinuousMap_ofContinuousMap (f : C(X, Y))
    (hf : ∀ (m : M) (x : X), f (m • x) = φ m • f x) :
    (ofContinuousMap f hf).toContinuousMap = f := rfl

@[simp]
theorem ofClass_apply {F : Type*} [FunLike F X Y] [ContinuousMapClass F X Y]
    [MulActionSemiHomClass F φ X Y] (f : F) (x : X) : ofClass f x = f x := rfl

/-- The scalar compatibility formula. -/
@[simp]
theorem map_smul (f : ContinuousMulActionHom φ X Y) (m : M) (x : X) :
    f (m • x) = φ m • f x :=
  map_smulₛₗ f m x

/-- The compact-open subspace topology, induced from continuous maps. -/
instance : TopologicalSpace (ContinuousMulActionHom φ X Y) :=
  TopologicalSpace.induced toContinuousMap inferInstance

/-- The forgetful map to continuous maps induces the topology. -/
theorem isInducing_toContinuousMap :
    Topology.IsInducing (toContinuousMap : ContinuousMulActionHom φ X Y → C(X, Y)) :=
  ⟨rfl⟩

/-- The forgetful map to continuous maps is continuous. -/
@[continuity, fun_prop]
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : ContinuousMulActionHom φ X Y → C(X, Y)) :=
  isInducing_toContinuousMap.continuous

/-- A family is continuous exactly when the corresponding compact-open family is. -/
theorem continuous_iff {T : Type*} [TopologicalSpace T]
    {f : T → ContinuousMulActionHom φ X Y} :
    Continuous f ↔ Continuous (fun t => (f t).toContinuousMap) :=
  isInducing_toContinuousMap.continuous_iff

/-- A family of continuous equivariant maps is continuous in the compact-open
subspace topology if its uncurried evaluation is continuous. No local compactness
or separation assumptions are needed. -/
theorem continuous_of_continuous_uncurry {T : Type*} [TopologicalSpace T]
    (f : T → ContinuousMulActionHom φ X Y)
    (h : Continuous (fun p : T × X => f p.1 p.2)) : Continuous f := by
  exact continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry (fun t => (f t).toContinuousMap) h)

instance : ContinuousEvalConst (ContinuousMulActionHom φ X Y) X Y :=
  ContinuousEvalConst.of_continuous_forget continuous_toContinuousMap

/-- The identity continuous equivariant map. -/
protected def id (M : Type u₁) (X : Type v₁) [SMul M X] [TopologicalSpace X] :
    ContinuousMulActionHom (@_root_.id M) X X :=
  ofMulActionHom (MulActionHom.id M) continuous_id

/-- Composition of continuous equivariant maps along compatible scalar maps. -/
def comp (g : ContinuousMulActionHom ψ Y Z) (f : ContinuousMulActionHom φ X Y)
    [CompTriple φ ψ χ] : ContinuousMulActionHom χ X Z :=
  ofMulActionHom (g.toMulActionHom.comp f.toMulActionHom)
    (g.continuous_toFun.comp f.continuous_toFun)

@[simp]
theorem id_apply (x : X) : ContinuousMulActionHom.id M X x = x := rfl

/-- Forgetting continuity preserves the identity map. -/
@[simp]
theorem toMulActionHom_id :
    (ContinuousMulActionHom.id M X).toMulActionHom = MulActionHom.id M := rfl

/-- Forgetting equivariance preserves the identity map. -/
@[simp]
theorem toContinuousMap_id :
    (ContinuousMulActionHom.id M X).toContinuousMap = ContinuousMap.id X := rfl

@[simp]
theorem comp_apply (g : ContinuousMulActionHom ψ Y Z) (f : ContinuousMulActionHom φ X Y)
    [CompTriple φ ψ χ] (x : X) : g.comp f x = g (f x) := rfl

/-- Forgetting continuity preserves composition. -/
@[simp]
theorem toMulActionHom_comp (g : ContinuousMulActionHom ψ Y Z)
    (f : ContinuousMulActionHom φ X Y) [CompTriple φ ψ χ] :
    (g.comp f).toMulActionHom = g.toMulActionHom.comp f.toMulActionHom := rfl

/-- Forgetting equivariance preserves composition. -/
@[simp]
theorem toContinuousMap_comp (g : ContinuousMulActionHom ψ Y Z)
    (f : ContinuousMulActionHom φ X Y) [CompTriple φ ψ χ] :
    (g.comp f).toContinuousMap = g.toContinuousMap.comp f.toContinuousMap := rfl

@[simp]
theorem id_comp (f : ContinuousMulActionHom φ X Y) :
    (ContinuousMulActionHom.id N Y).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : ContinuousMulActionHom φ X Y) :
    f.comp (ContinuousMulActionHom.id M X) = f :=
  ext fun _ => rfl

end ContinuousMulActionHom
