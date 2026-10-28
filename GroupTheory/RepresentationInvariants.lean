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
public import GroupTheory.LinearAlgebra.Prod

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
restriction to fixed submodules is injective. The kernel of any restriction is the
ambient kernel pulled back along the source fixed-submodule inclusion. For an injective
intertwining map, the restricted range is the ambient range pulled back along the target
fixed-submodule inclusion. Consequently, a bijective intertwining map restricts to a
bijection on fixed submodules. If `f` is injective and `f, g` are exact on the ambient
modules, their restrictions are exact as well. These statements require only a semiring,
a monoid, and additive commutative monoids with their given module structures; all carrier
universes are independent.

The exactness argument compares the restricted kernel and range through their pullback
identities and the ambient kernel-range equality. This is left exactness, not a claim
that fixed vectors preserve surjections.

The fixed submodule of the stock product representation is literally the product of
the two fixed submodules. `fixedSubmoduleProdEquiv` splits its coordinates by reusing
`Submodule.prodEquiv` after transport along this equality. Its projection and inclusion
identities stay on the original modules, and it is natural in two supplied intertwining
maps. The product module structure is the usual one induced by the given factors.

For a group representation over a commutative ring on an additive commutative group,
`Representation.fixedSubmodule_eq_invariants` identifies this submodule with
`Representation.invariants` on the same representation and module data. The theorem
`Representation.invariants_prod` gives the corresponding product identity. Rewriting
`fixedSubmoduleProdEquiv` by the three same-data equalities gives the linear equivalence
between product invariants and the product of invariants, with the same coordinates.

## Examples and boundary

Let the free monoid on one generator act on `ℕ²` by swapping coordinates. Its fixed
vectors are the diagonal pairs. The split sequence `ℕ² → ℕ² × ℕ² → ℕ²`, given by
`a ↦ (a, 0)` and `(a, b) ↦ b` with the product action, has an injective first map
and is exact both before and after restriction. This uses neither a group as the acting
monoid nor additive inverses in the modules.

For two different factors, let `Multiplicative ℕ` act on `ℕ²` by powers of the swap
and on `ℕ³` by powers of the cyclic rotation. Their fixed submodules are respectively
`{(a, a)}` and `{(b, b, b)}`. The product equivalence splits
`((a, a), (b, b, b))` into these two independent fixed vectors. Both fixed submodules
are proper and nonzero; the acting monoid is infinite and is not a group.

For contrast, let the cyclic group of order two act by sign on `ℤ`. Multiplication by
two followed by reduction modulo two is exact and equivariant, with trivial action on
`ℤ / 2ℤ`. The integer fixed submodules are zero, whereas every residue class is fixed.
Thus the restricted reduction map is not surjective, even though the ambient map is.
Its restricted range is zero, but the pullback of its ambient range along the target
fixed-submodule inclusion is the whole nonzero target. This also shows why the range
formula `IntertwiningMap.range_fixedSubmoduleMap` requires injectivity.

## References

This construction generalizes Mathlib's `Representation.invariants`, due to Antoine
Labelle. It uses Mathlib's `Representation.IntertwiningMap` API (Stepan Nesterov and
Edison Xie) and `LinearMap.codRestrict` API (in a file authored by Mario Carneiro).
The reference revision is `83abb3e776bdefcbc447a1e44d0debe4010039e5`, in
`Mathlib.RepresentationTheory.Basic`, `Mathlib.RepresentationTheory.Invariants`,
`Mathlib.RepresentationTheory.Intertwining`, and
`Mathlib.Algebra.Module.Submodule.LinearMap`. The left-exactness proof uses
`LinearMap.exact_iff` from `Mathlib.Algebra.Exact.Basic`, formalized by Antoine
Chambert-Loir. The kernel formula reuses `LinearMap.ker_codRestrict` and
`LinearMap.ker_comp` from `Mathlib.Algebra.Module.Submodule.Ker`, authored by Johannes
Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis, and Heather Macbeth.
The range and bijectivity results also use `LinearMap.range_eq_top` and
`Submodule.comap_top` from `Mathlib.Algebra.Module.Submodule.Range` and
`Mathlib.Algebra.Module.Submodule.Map`.
The product result reuses the same fixed-submodule restrictions, Mathlib's stock
product representation and public intertwining projections and pairing, together with
its product-submodule API and `LinearEquiv.ofEq`. The generic splitting equivalence
is in `GroupTheory.LinearAlgebra.Prod`, separately from the representation results.
-/

@[expose] public section

universe uR uG uV uW uU uV' uW'

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

/-- Pairing two intertwining maps with a common domain pairs their values. -/
@[simp]
theorem prod_apply (f : IntertwiningMap ρ σ) (g : IntertwiningMap ρ τ) (v : V) :
    f.prod g v = (f v, g v) := rfl

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

/-- The kernel of an intertwining map on fixed submodules is the pullback of
its ambient kernel along the source fixed-submodule inclusion. -/
theorem ker_fixedSubmoduleMap (f : IntertwiningMap ρ σ) :
    LinearMap.ker f.fixedSubmoduleMap =
      (LinearMap.ker f.toLinearMap).comap (fixedSubmodule ρ).subtype := by
  exact
    (LinearMap.ker_codRestrict (fixedSubmodule σ)
      (f.toLinearMap.comp (fixedSubmodule ρ).subtype)
      (fun v g =>
        (Representation.IntertwiningMap.isIntertwining ρ σ f g (v : V)).symm.trans
          (congrArg f (apply_coe_fixedSubmodule ρ g v)))).trans
      (LinearMap.ker_comp (fixedSubmodule ρ).subtype f.toLinearMap)

/-- The range of an injective intertwining map on fixed submodules is the pullback of
its ambient range along the target fixed-submodule inclusion. -/
theorem range_fixedSubmoduleMap (f : IntertwiningMap ρ σ)
    (hf : Function.Injective f) :
    LinearMap.range f.fixedSubmoduleMap =
      (LinearMap.range f.toLinearMap).comap (fixedSubmodule σ).subtype := by
  ext b
  simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.subtype_apply,
    toLinearMap_apply]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(a : V), (fixedSubmoduleMap_apply f a).symm⟩
  · rintro ⟨a, ha⟩
    have ha_fixed : a ∈ fixedSubmodule ρ :=
      f.mem_fixedSubmodule_of_apply_mem hf (ha.symm ▸ b.property)
    refine ⟨⟨a, ha_fixed⟩, ?_⟩
    apply Subtype.ext
    simpa only [fixedSubmoduleMap_apply] using ha

/-- A bijective intertwining map restricts to a bijection between fixed submodules. -/
theorem fixedSubmoduleMap_bijective (f : IntertwiningMap ρ σ)
    (hf : Function.Bijective f) : Function.Bijective f.fixedSubmoduleMap := by
  refine ⟨f.fixedSubmoduleMap_injective hf.1, ?_⟩
  apply LinearMap.range_eq_top.mp
  have hf_range : LinearMap.range f.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hf.2
  rw [f.range_fixedSubmoduleMap hf.1, hf_range, Submodule.comap_top]

/-- Fixed vectors preserve exactness at the middle term when the first ambient
intertwining map is injective. The kernel and range pullback identities transfer ambient
exactness; no surjectivity of the restricted second map is asserted. -/
theorem fixedSubmoduleMap_exact (f : IntertwiningMap ρ σ) (g : IntertwiningMap σ τ)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact f.fixedSubmoduleMap g.fixedSubmoduleMap := by
  apply LinearMap.exact_iff.mpr
  rw [g.ker_fixedSubmoduleMap, f.range_fixedSubmoduleMap hf,
    (LinearMap.exact_iff (f := f.toLinearMap) (g := g.toLinearMap)).mp hfg]

end IntertwiningMap

end IntertwiningMap

section Prod

variable [AddCommMonoid W] [Module R W]

/-- A pair is fixed by the product representation exactly when both coordinates are fixed. -/
theorem mem_fixedSubmodule_prod (ρ : Representation R G V) (τ : Representation R G W)
    (p : V × W) :
    p ∈ (ρ.prod τ).fixedSubmodule ↔
      p.1 ∈ ρ.fixedSubmodule ∧ p.2 ∈ τ.fixedSubmodule := by
  rcases p with ⟨v, w⟩
  simp [mem_fixedSubmodule, forall_and]

/-- The fixed submodule of a product is the product of the original fixed submodules. -/
theorem fixedSubmodule_prod (ρ : Representation R G V) (τ : Representation R G W) :
    (ρ.prod τ).fixedSubmodule = ρ.fixedSubmodule.prod τ.fixedSubmodule := by
  ext p
  exact (mem_fixedSubmodule_prod ρ τ p).trans Submodule.mem_prod.symm

/-- The fixed vectors of a product representation split into the fixed vectors of its factors.
This is transport along `fixedSubmodule_prod` followed by the generic `Submodule.prodEquiv`. -/
noncomputable def fixedSubmoduleProdEquiv (ρ : Representation R G V) (τ : Representation R G W) :
    (ρ.prod τ).fixedSubmodule ≃ₗ[R] ρ.fixedSubmodule × τ.fixedSubmodule :=
  (LinearEquiv.ofEq _ _ (fixedSubmodule_prod ρ τ)).trans
    (Submodule.prodEquiv ρ.fixedSubmodule τ.fixedSubmodule)

/-- Splitting a fixed vector preserves its original first coordinate. -/
@[simp]
theorem fixedSubmoduleProdEquiv_apply_fst (ρ : Representation R G V)
    (τ : Representation R G W) (z : (ρ.prod τ).fixedSubmodule) :
    ((fixedSubmoduleProdEquiv ρ τ z).1 : V) = (z : V × W).1 :=
  Submodule.prodEquiv_apply_fst _ _ (LinearEquiv.ofEq _ _ (fixedSubmodule_prod ρ τ) z)

/-- Splitting a fixed vector preserves its original second coordinate. -/
@[simp]
theorem fixedSubmoduleProdEquiv_apply_snd (ρ : Representation R G V)
    (τ : Representation R G W) (z : (ρ.prod τ).fixedSubmodule) :
    ((fixedSubmoduleProdEquiv ρ τ z).2 : W) = (z : V × W).2 :=
  Submodule.prodEquiv_apply_snd _ _ (LinearEquiv.ofEq _ _ (fixedSubmodule_prod ρ τ) z)

/-- The inverse fixed-product equivalence joins the original ambient coordinates. -/
@[simp]
theorem coe_fixedSubmoduleProdEquiv_symm_apply (ρ : Representation R G V)
    (τ : Representation R G W) (p : ρ.fixedSubmodule × τ.fixedSubmodule) :
    ((fixedSubmoduleProdEquiv ρ τ).symm p : V × W) = ((p.1 : V), (p.2 : W)) :=
  Submodule.coe_prodEquiv_symm_apply _ _ p

/-- The fixed-product equivalence is the pairing of the existing restricted projections. -/
theorem fixedSubmoduleProdEquiv_toLinearMap (ρ : Representation R G V)
    (τ : Representation R G W) :
    (fixedSubmoduleProdEquiv ρ τ).toLinearMap =
      (IntertwiningMap.fst R ρ τ).fixedSubmoduleMap.prod
        (IntertwiningMap.snd R ρ τ).fixedSubmoduleMap := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    change ((fixedSubmoduleProdEquiv ρ τ z).1 : V) =
      ((IntertwiningMap.fst R ρ τ).fixedSubmoduleMap z : V)
    rw [fixedSubmoduleProdEquiv_apply_fst, IntertwiningMap.fixedSubmoduleMap_apply,
      IntertwiningMap.fst_apply]
  · apply Subtype.ext
    change ((fixedSubmoduleProdEquiv ρ τ z).2 : W) =
      ((IntertwiningMap.snd R ρ τ).fixedSubmoduleMap z : W)
    rw [fixedSubmoduleProdEquiv_apply_snd, IntertwiningMap.fixedSubmoduleMap_apply,
      IntertwiningMap.snd_apply]

/-- Splitting fixed vectors commutes with the inclusions into the original product module. -/
theorem subtype_prodMap_comp_fixedSubmoduleProdEquiv (ρ : Representation R G V)
    (τ : Representation R G W) :
    (ρ.fixedSubmodule.subtype.prodMap τ.fixedSubmodule.subtype).comp
        (fixedSubmoduleProdEquiv ρ τ).toLinearMap = (ρ.prod τ).fixedSubmodule.subtype := by
  apply LinearMap.ext
  intro z
  change (((fixedSubmoduleProdEquiv ρ τ z).1 : V),
    ((fixedSubmoduleProdEquiv ρ τ z).2 : W)) = (z : V × W)
  exact Prod.ext (fixedSubmoduleProdEquiv_apply_fst ρ τ z)
    (fixedSubmoduleProdEquiv_apply_snd ρ τ z)

variable {V' : Type uV'} {W' : Type uW'}
variable [AddCommMonoid V'] [Module R V'] [AddCommMonoid W'] [Module R W']
variable {ρ : Representation R G V} {τ : Representation R G W}
variable {ρ' : Representation R G V'} {τ' : Representation R G W'}

/-- Splitting fixed vectors is natural in a pair of supplied intertwining maps.
The product intertwiner uses only the stock projections, composition and pairing. -/
theorem fixedSubmoduleProdEquiv_naturality (f : IntertwiningMap ρ ρ')
    (k : IntertwiningMap τ τ') :
    (fixedSubmoduleProdEquiv ρ' τ').toLinearMap.comp
        ((f.comp (IntertwiningMap.fst R ρ τ)).prod
          (k.comp (IntertwiningMap.snd R ρ τ))).fixedSubmoduleMap =
      (f.fixedSubmoduleMap.prodMap k.fixedSubmoduleMap).comp
        (fixedSubmoduleProdEquiv ρ τ).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearEquiv.coe_coe,
      fixedSubmoduleProdEquiv_apply_fst, IntertwiningMap.fixedSubmoduleMap_apply,
      IntertwiningMap.prod_apply, IntertwiningMap.comp_apply, IntertwiningMap.fst_apply]
  · apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearEquiv.coe_coe,
      fixedSubmoduleProdEquiv_apply_snd, IntertwiningMap.fixedSubmoduleMap_apply,
      IntertwiningMap.prod_apply, IntertwiningMap.comp_apply, IntertwiningMap.snd_apply]

end Prod

end Semiring

section CommRing

variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- On the same group representation and module data, the fixed submodule is Mathlib's
invariant submodule. -/
theorem fixedSubmodule_eq_invariants (ρ : Representation R G V) :
    fixedSubmodule ρ = invariants ρ := by
  ext v
  rfl

variable [AddCommGroup W] [Module R W]

/-- On the same group representations and module data, invariants commute with products. -/
theorem invariants_prod (ρ : Representation R G V) (τ : Representation R G W) :
    (ρ.prod τ).invariants = ρ.invariants.prod τ.invariants := by
  simpa only [fixedSubmodule_eq_invariants] using fixedSubmodule_prod ρ τ

end CommRing

end Representation
