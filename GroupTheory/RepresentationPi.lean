/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.LinearAlgebra.Pi
public import GroupTheory.RepresentationInvariants

/-!
# Fixed vectors of arbitrary indexed products

`Representation.pi` acts coordinatewise on the original dependent-function module.
`isIntertwiningMap_pi_iff` characterizes maps into it by their coordinates. Together
with Mathlib's linear-product construction and reconstruction laws, this gives the
unique map with any supplied intertwining coordinates.

`fixedSubmodule_pi` identifies its fixed submodule with the full indexed product of
the original fixed submodules. `fixedSubmodulePiEquiv` is equality transport followed
by the generic `Submodule.piEquiv`, not a second inverse construction. Its forward
and inverse coordinates, inclusion identity and naturality use the original modules
and actions. The index may be infinite or empty; only a semiring, a monoid and the
given additive commutative monoid modules are required. The scalar, acting-monoid,
index, source-fiber, target-fiber and auxiliary-source universes are independent.

In the separate commutative-ring, group and additive-group context, `invariants_pi`
follows from the existing same-data fixed-submodule/invariants bridge.

## Examples and boundary

Let the free monoid on one generator act on `ℕ × ℕ` by coordinate swap, over `ℕ`.
Each fixed submodule is the proper nonzero diagonal. Over index type `ℕ`, the
all-`(1, 1)` sequence is fixed and has infinite support, whereas a sequence with
`(1, 0)` at one coordinate is not fixed. Thus the product is neither a direct sum
nor a construction in which all vectors are fixed. Coordinatewise doubling is a
nonidentity intertwiner, and the naturality identity preserves its coordinates.

The same monoid can instead act by powers of the noninvertible linear projection
`(a, b) ↦ (a, 0)`. The fixed fiber is the proper nonzero horizontal axis, so the
construction does not require the action maps to be automorphisms. For an empty
index type, both sides have the unique empty function and the fixed submodule is
the whole original product, without any nonempty-index guard.

## References

The construction reuses the fixed-vector and restricted-intertwiner API in
`GroupTheory.RepresentationInvariants`, which generalizes Antoine Labelle's Mathlib
invariants. Pointwise maps are bundled by Mathlib's intertwining-map API of Stepan
Nesterov and Edison Xie. The linear-product, projection and reconstruction API is
from `Mathlib.LinearAlgebra.Pi`, by Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
Yury Kudryashov and Eric Wieser. The generic splitting in
`GroupTheory.LinearAlgebra.Pi` enriches Mathlib's subtype equivalences; equality
transport uses `LinearEquiv.ofEq`.
-/

@[expose] public section

universe uR uG uI uM uN uA

namespace Representation

variable {R : Type uR} {G : Type uG} {I : Type uI} {M : I → Type uM}

section Semiring

variable [Semiring R] [Monoid G]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The coordinatewise representation on the original dependent-function module. -/
def pi (ρ : ∀ i, Representation R G (M i)) : Representation R G (∀ i, M i) where
  toFun g := LinearMap.piMap (fun i => ρ i g)
  map_one' := by
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun f : Module.End R (M i) => f (x i)) ((ρ i).map_one)
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    funext i
    exact congrArg (fun f : Module.End R (M i) => f (x i)) ((ρ i).map_mul g h)

/-- The indexed representation acts by the given action at each coordinate. -/
@[simp]
theorem pi_apply (ρ : ∀ i, Representation R G (M i))
    (g : G) (x : ∀ i, M i) (i : I) :
    pi ρ g x i = ρ i g (x i) := rfl

section UniversalProperty

variable {A : Type uA} [AddCommMonoid A] [Module R A]

/-- A map into the indexed representation intertwines exactly when every coordinate does. -/
theorem isIntertwiningMap_pi_iff (ρ : ∀ i, Representation R G (M i))
    (σ : Representation R G A) (f : A →ₗ[R] (∀ i, M i)) :
    IsIntertwiningMap σ (pi ρ) f ↔
      ∀ i, IsIntertwiningMap σ (ρ i) ((LinearMap.proj i).comp f) := by
  constructor
  · intro hf i
    refine ⟨fun g a => ?_⟩
    simpa only [LinearMap.comp_apply, LinearMap.proj_apply, pi_apply] using
      congrFun (hf.isIntertwining g a) i
  · intro hf
    refine ⟨fun g a => ?_⟩
    funext i
    simpa only [LinearMap.comp_apply, LinearMap.proj_apply, pi_apply] using
      (hf i).isIntertwining g a

/-- Supplied intertwining coordinates determine a unique intertwining linear map into
the indexed representation. The map and its uniqueness use the usual linear-product API. -/
theorem existsUnique_isIntertwiningMap_pi (ρ : ∀ i, Representation R G (M i))
    (σ : Representation R G A) (f : ∀ i, A →ₗ[R] M i)
    (hf : ∀ i, IsIntertwiningMap σ (ρ i) (f i)) :
    ∃! F : A →ₗ[R] (∀ i, M i),
      IsIntertwiningMap σ (pi ρ) F ∧ ∀ i, (LinearMap.proj i).comp F = f i := by
  refine ⟨LinearMap.pi f, ⟨?_, fun i => LinearMap.proj_pi f i⟩, ?_⟩
  · apply (isIntertwiningMap_pi_iff ρ σ (LinearMap.pi f)).mpr
    intro i
    simpa only [LinearMap.proj_pi] using hf i
  · intro F hF
    calc
      F = LinearMap.pi (fun i => (LinearMap.proj i).comp F) :=
        (LinearMap.pi_proj_comp F).symm
      _ = LinearMap.pi f := congrArg LinearMap.pi (funext hF.2)

end UniversalProperty

/-- A product vector is fixed exactly when all its original coordinates are fixed. -/
theorem mem_fixedSubmodule_pi (ρ : ∀ i, Representation R G (M i)) (x : ∀ i, M i) :
    x ∈ (pi ρ).fixedSubmodule ↔ ∀ i, x i ∈ (ρ i).fixedSubmodule := by
  constructor
  · intro hx i
    apply (mem_fixedSubmodule (ρ i) (x i)).mpr
    intro g
    simpa only [pi_apply] using
      congrFun ((mem_fixedSubmodule (pi ρ) x).mp hx g) i
  · intro hx
    apply (mem_fixedSubmodule (pi ρ) x).mpr
    intro g
    funext i
    exact (pi_apply ρ g x i).trans ((mem_fixedSubmodule (ρ i) (x i)).mp (hx i) g)

/-- Fixed submodules commute with arbitrary indexed products on the original modules. -/
theorem fixedSubmodule_pi (ρ : ∀ i, Representation R G (M i)) :
    (pi ρ).fixedSubmodule = Submodule.pi Set.univ (fun i => (ρ i).fixedSubmodule) := by
  ext x
  simp only [mem_fixedSubmodule_pi, Submodule.mem_pi, Set.mem_univ, forall_const]

/-- The fixed vectors of an indexed product split into their original fixed coordinates.
This is equality transport along `fixedSubmodule_pi`, followed by `Submodule.piEquiv`. -/
noncomputable def fixedSubmodulePiEquiv (ρ : ∀ i, Representation R G (M i)) :
    (pi ρ).fixedSubmodule ≃ₗ[R] (∀ i, (ρ i).fixedSubmodule) :=
  (LinearEquiv.ofEq _ _ (fixedSubmodule_pi ρ)).trans
    (Submodule.piEquiv (fun i => (ρ i).fixedSubmodule))

/-- Splitting a fixed product vector preserves every original ambient coordinate. -/
@[simp]
theorem fixedSubmodulePiEquiv_apply (ρ : ∀ i, Representation R G (M i))
    (z : (pi ρ).fixedSubmodule) (i : I) :
    (fixedSubmodulePiEquiv ρ z i : M i) = (z : ∀ i, M i) i :=
  Submodule.piEquiv_apply _ (LinearEquiv.ofEq _ _ (fixedSubmodule_pi ρ) z) i

/-- The inverse fixed-product equivalence assembles the original ambient coordinates. -/
@[simp]
theorem coe_fixedSubmodulePiEquiv_symm_apply (ρ : ∀ i, Representation R G (M i))
    (y : ∀ i, (ρ i).fixedSubmodule) (i : I) :
    ((fixedSubmodulePiEquiv ρ).symm y : ∀ i, M i) i = (y i : M i) :=
  Submodule.coe_piEquiv_symm_apply _ y i

/-- Splitting fixed vectors commutes with the inclusions into the original product module. -/
theorem subtype_piMap_comp_fixedSubmodulePiEquiv (ρ : ∀ i, Representation R G (M i)) :
    (LinearMap.piMap (fun i => (ρ i).fixedSubmodule.subtype)).comp
        (fixedSubmodulePiEquiv ρ).toLinearMap = (pi ρ).fixedSubmodule.subtype := by
  apply LinearMap.ext
  intro z
  funext i
  simpa only [LinearMap.comp_apply, LinearMap.piMap_apply, LinearEquiv.coe_coe,
    Submodule.subtype_apply] using fixedSubmodulePiEquiv_apply ρ z i

section Naturality

variable {N : I → Type uN}
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Splitting fixed vectors is natural in a supplied family of intertwining maps.
The product intertwiner bundles the stock pointwise linear map with derived compatibility. -/
theorem fixedSubmodulePiEquiv_naturality (ρ : ∀ i, Representation R G (M i))
    (τ : ∀ i, Representation R G (N i)) (f : ∀ i, IntertwiningMap (ρ i) (τ i)) :
    let F : IntertwiningMap (pi ρ) (pi τ) :=
      (LinearMap.piMap (fun i => (f i).toLinearMap)).intertwiningMap_of_isIntertwiningMap
        (pi ρ) (pi τ) (by
          intro g x
          funext i
          simpa only [pi_apply, LinearMap.piMap_apply, IntertwiningMap.toLinearMap_apply] using
            Representation.IntertwiningMap.isIntertwining (ρ i) (τ i) (f i) g (x i))
    (fixedSubmodulePiEquiv τ).toLinearMap.comp F.fixedSubmoduleMap =
      (LinearMap.piMap (fun i => (f i).fixedSubmoduleMap)).comp
        (fixedSubmodulePiEquiv ρ).toLinearMap := by
  dsimp only
  apply LinearMap.ext
  intro z
  funext i
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.piMap_apply, LinearEquiv.coe_coe,
    fixedSubmodulePiEquiv_apply, IntertwiningMap.fixedSubmoduleMap_apply,
    LinearMap.toIntertwiningMap, IntertwiningMap.toLinearMap_apply]

end Naturality

end Semiring

section CommRing

variable [CommRing R] [Group G]
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- On the same group representations and module data, invariants commute with indexed products. -/
theorem invariants_pi (ρ : ∀ i, Representation R G (M i)) :
    (pi ρ).invariants = Submodule.pi Set.univ (fun i => (ρ i).invariants) := by
  simpa only [fixedSubmodule_eq_invariants] using fixedSubmodule_pi ρ

end CommRing

end Representation
