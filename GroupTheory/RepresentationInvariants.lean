/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

/-
The fixed-submodule construction is adapted from Mathlib's representation invariants.
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Exact.Basic

/-!
# Fixed vectors of a representation over a semiring

For a monoid representation on a module over a semiring, `Representation.fixedSubmodule`
is the submodule of vectors fixed by every element of the monoid. It uses the given
module structure on the representation's underlying additive commutative monoid.

The inclusion is the usual `Submodule.subtype`. A linear map whose values are fixed
factors uniquely through this inclusion using `LinearMap.codRestrict`; its pointwise
formula is the existing `LinearMap.codRestrict_apply`. Bundled intertwining maps induce
linear maps between fixed submodules, commuting with the inclusions and preserving
identity and composition. An injective intertwining map reflects fixedness, and its
restriction to fixed submodules is injective. If `f` is injective and `f, g` are exact
on the ambient modules, their restrictions are exact as well. These statements require
only a semiring, a monoid, and additive commutative monoids with their given module
structures; all carrier universes are independent.

The exactness argument lifts a fixed vector in the kernel along the ambient map `f`.
Equivariance and injectivity of `f` force that lift to be fixed. The reverse inclusion
follows from the ambient exactness. This is left exactness, not a claim that fixed
vectors preserve surjections.

For a group representation over a commutative ring on an additive commutative group,
`Representation.fixedSubmodule_eq_invariants` identifies this submodule with
`Representation.invariants` on the same representation and module data.

## Examples and boundary

Let the free monoid on one generator act on `ℕ²` by swapping coordinates. Its fixed
vectors are the diagonal pairs. The split sequence `ℕ² → ℕ² × ℕ² → ℕ²`, given by
`a ↦ (a, 0)` and `(a, b) ↦ b` with the product action, has an injective first map
and is exact both before and after restriction. This uses neither a group as the acting
monoid nor additive inverses in the modules.

For contrast, let the cyclic group of order two act by sign on `ℤ`. Multiplication by
two followed by reduction modulo two is exact and equivariant, with trivial action on
`ℤ / 2ℤ`. The integer fixed submodules are zero, whereas every residue class is fixed.
Thus the restricted reduction map is not surjective, even though the ambient map is.

## References

This construction generalizes Mathlib's `Representation.invariants`, due to Antoine
Labelle. It uses Mathlib's `Representation.IntertwiningMap` API (Stepan Nesterov and
Edison Xie) and `LinearMap.codRestrict` API (in a file authored by Mario Carneiro).
The reference revision is `83abb3e776bdefcbc447a1e44d0debe4010039e5`, in
`Mathlib.RepresentationTheory.Basic`, `Mathlib.RepresentationTheory.Invariants`,
`Mathlib.RepresentationTheory.Intertwining`, and
`Mathlib.Algebra.Module.Submodule.LinearMap`. The left-exactness proof uses
`LinearMap.exact_iff` from `Mathlib.Algebra.Exact.Basic`, formalized by Antoine
Chambert-Loir, together with Mathlib's kernel and range membership APIs.
-/

@[expose] public section

universe uR uG uV uW uU

namespace Representation

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}

section Semiring

variable [Semiring R] [Monoid G] [AddCommMonoid V] [Module R V]

/-- The submodule of vectors fixed by every element of a monoid representation. -/
def fixedSubmodule (ρ : Representation R G V) : Submodule R V where
  carrier := {v | ∀ g : G, ρ g v = v}
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

/-- Membership in the fixed submodule is exactly the fixed-vector condition. -/
@[simp]
theorem mem_fixedSubmodule (ρ : Representation R G V) (v : V) :
    v ∈ fixedSubmodule ρ ↔ ∀ g : G, ρ g v = v := Iff.rfl

/-- The action fixes the underlying vector of every element of the fixed submodule. -/
@[simp]
theorem apply_coe_fixedSubmodule (ρ : Representation R G V) (g : G)
    (v : fixedSubmodule ρ) : ρ g (v : V) = (v : V) := v.property g

section LinearMap

variable [AddCommMonoid W] [Module R W]

/-- The `codRestrict` factorization through the fixed submodule's inclusion is unique. -/
theorem fixedSubmodule_codRestrict_unique (ρ : Representation R G V)
    (t : W →ₗ[R] V) (ht : ∀ g w, ρ g (t w) = t w)
    (l : W →ₗ[R] fixedSubmodule ρ) (hl : (fixedSubmodule ρ).subtype.comp l = t) :
    l = LinearMap.codRestrict (fixedSubmodule ρ) t (fun w g => ht g w) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  exact congrArg (fun q : W →ₗ[R] V => q w) hl

end LinearMap

section IntertwiningMap

variable [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]
variable {ρ : Representation R G V} {σ : Representation R G W} {τ : Representation R G U}

namespace IntertwiningMap

/-- An intertwining map restricts to a linear map between the fixed submodules. -/
def fixedSubmoduleMap (f : IntertwiningMap ρ σ) :
    fixedSubmodule ρ →ₗ[R] fixedSubmodule σ :=
  LinearMap.codRestrict (fixedSubmodule σ)
    (f.toLinearMap.comp (fixedSubmodule ρ).subtype)
    (fun v g =>
      (Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)).symm.trans
        (congrArg f (apply_coe_fixedSubmodule ρ g v)))

/-- Restricting an intertwining map does not change its value in the ambient module. -/
@[simp]
theorem fixedSubmoduleMap_apply (f : IntertwiningMap ρ σ) (v : fixedSubmodule ρ) :
    (f.fixedSubmoduleMap v : W) = f (v : V) := rfl

/-- The map on fixed submodules commutes with the inclusions into the ambient modules. -/
theorem subtype_comp_fixedSubmoduleMap (f : IntertwiningMap ρ σ) :
    (fixedSubmodule σ).subtype.comp f.fixedSubmoduleMap =
      f.toLinearMap.comp (fixedSubmodule ρ).subtype :=
  LinearMap.subtype_comp_codRestrict
    (f := f.toLinearMap.comp (fixedSubmodule ρ).subtype) (fixedSubmodule σ)
    (fun v g =>
      (Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)).symm.trans
        (congrArg f (apply_coe_fixedSubmodule ρ g v)))

/-- Restriction of the identity intertwining map is the identity linear map. -/
@[simp]
theorem fixedSubmoduleMap_id (ρ : Representation R G V) :
    (IntertwiningMap.id ρ).fixedSubmoduleMap = LinearMap.id := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rfl

/-- Restriction of a composite intertwining map is the composite of its restrictions. -/
@[simp]
theorem fixedSubmoduleMap_comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f.comp g).fixedSubmoduleMap = f.fixedSubmoduleMap.comp g.fixedSubmoduleMap := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rfl

/-- An injective intertwining map reflects membership in the fixed submodule. -/
theorem mem_fixedSubmodule_of_apply_mem (f : IntertwiningMap ρ σ)
    (hf : Function.Injective f) {v : V} (hv : f v ∈ fixedSubmodule σ) :
    v ∈ fixedSubmodule ρ := by
  apply (mem_fixedSubmodule ρ v).2
  intro x
  apply hf
  calc
    f (ρ x v) = σ x (f v) := Representation.IntertwiningMap.isIntertwining ρ σ f x v
    _ = f v := (mem_fixedSubmodule σ (f v)).1 hv x

/-- The restriction of an injective intertwining map to fixed submodules is injective. -/
theorem fixedSubmoduleMap_injective (f : IntertwiningMap ρ σ)
    (hf : Function.Injective f) : Function.Injective f.fixedSubmoduleMap := by
  intro v w h
  apply Subtype.ext
  apply hf
  simpa only [fixedSubmoduleMap_apply] using
    congrArg (fun z : fixedSubmodule σ => (z : W)) h

/-- Fixed vectors preserve exactness at the middle term when the first ambient
intertwining map is injective. Equivariance and injectivity make every lift of a fixed
kernel vector fixed; no surjectivity of the restricted second map is asserted. -/
theorem fixedSubmoduleMap_exact (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact f.fixedSubmoduleMap g.fixedSubmoduleMap := by
  have hker : LinearMap.ker g.toLinearMap = LinearMap.range f.toLinearMap :=
    LinearMap.exact_iff.mp hfg
  apply LinearMap.exact_iff.mpr
  ext b
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hb
    have hgb : g (b : W) = 0 := by
      simpa only [fixedSubmoduleMap_apply, Submodule.coe_zero] using
        congrArg (fun z : fixedSubmodule τ => (z : U)) hb
    have hb_range : (b : W) ∈ LinearMap.range f.toLinearMap := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr hgb
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hb_range
    have ha_fixed : a ∈ fixedSubmodule ρ :=
      f.mem_fixedSubmodule_of_apply_mem hf (ha.symm ▸ b.property)
    refine ⟨⟨a, ha_fixed⟩, ?_⟩
    apply Subtype.ext
    simpa only [fixedSubmoduleMap_apply, toLinearMap_apply] using ha
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    have hfa : f (a : V) ∈ LinearMap.ker g.toLinearMap := by
      rw [hker]
      exact LinearMap.mem_range.mpr ⟨(a : V), rfl⟩
    simpa only [fixedSubmoduleMap_apply, Submodule.coe_zero, toLinearMap_apply] using
      (LinearMap.mem_ker.mp hfa)

end IntertwiningMap

end IntertwiningMap

end Semiring

section CommRing

variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- On the same group representation and module data, the fixed submodule is Mathlib's
invariant submodule. -/
theorem fixedSubmodule_eq_invariants (ρ : Representation R G V) :
    fixedSubmodule ρ = invariants ρ := by
  ext v
  rfl

end CommRing

end Representation
