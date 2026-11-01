/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Pontryagin dual transport and bidual evaluation

Precomposition by a continuous multiplicative equivalence gives a continuous
multiplicative equivalence of the entire Pontryagin duals with their compact-open
topologies. The direction is contravariant: an equivalence `A ≃ₜ* B` gives
`PontryaginDual B ≃ₜ* PontryaginDual A`. This transport requires only monoids with
topologies, without local compactness or continuity of their operations.

For a monoid with a topology, evaluation at a point is a continuous circle-valued
character of its Pontryagin dual. When the monoid and the circle form a locally
compact pair, these characters assemble into a continuous homomorphism to the
bidual, equipped with its iterated compact-open topology.

The evaluation homomorphism is natural under continuous monoid homomorphisms.
If the dual and the circle also form a locally compact pair, evaluation on the
dual is a section of the dual of evaluation. This triangular identity does not
assert that evaluation on the original monoid is an isomorphism.

## Main definitions

* `PontryaginDual.mapEquiv`: contravariant transport of the whole compact-open dual
  along a continuous multiplicative equivalence.
* `PontryaginDual.eval`: the canonical continuous homomorphism into the bidual.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.10)–(1.1.11), for canonical bidual evaluation and its naturality.
* Mathlib's `Topology.Algebra.PontryaginDual` and
  `Topology.Algebra.ContinuousMonoidHom`, for `PontryaginDual.map` and continuous
  multiplicative equivalences.
* Mathlib's `Topology.Algebra.Group.CompactOpen`, for fixed precomposition via
  `ContinuousMonoidHom.compLeft` and `ContinuousMonoidHom.continuous_comp_left`,
  and, with `Topology.CompactOpen`, for compact-open evaluation and currying on
  the existing continuous homomorphism spaces.
* Mathlib's `MonoidHom.eval` and `AddChar.doubleDualEmb` are algebraic counterparts;
  `AddChar.doubleDualEquiv` in `Analysis.Fourier.FiniteAbelian.PontryaginDuality`
  gives finite-character biduality. Those abstract-character models are not
  substituted for the continuous characters or topologies used here.
-/

@[expose] public section

universe u v

namespace PontryaginDual

section MapEquiv

/-- Precomposition by a continuous multiplicative equivalence, as a contravariant
continuous multiplicative equivalence of the whole compact-open Pontryagin duals.
Its inverse is precomposition by the inverse equivalence. -/
noncomputable def mapEquiv {A : Type u} {B : Type v} [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ* B) :
    PontryaginDual B ≃ₜ* PontryaginDual A where
  toFun := map (e : A →ₜ* B)
  invFun := map (e.symm : B →ₜ* A)
  left_inv := by
    intro χ
    refine PontryaginDual.ext fun b => ?_
    simp only [map_apply, ContinuousMonoidHom.coe_coe, e.apply_symm_apply]
  right_inv := by
    intro ψ
    refine PontryaginDual.ext fun a => ?_
    simp only [map_apply, ContinuousMonoidHom.coe_coe, e.symm_apply_apply]
  map_mul' := _root_.map_mul (map (e : A →ₜ* B))
  continuous_toFun := (map (e : A →ₜ* B)).continuous
  continuous_invFun := (map (e.symm : B →ₜ* A)).continuous

variable {A : Type u} {B : Type v}
variable [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

/-- The continuous homomorphism underlying dual transport is the dual map. -/
@[simp] theorem mapEquiv_toContinuousMonoidHom (e : A ≃ₜ* B) :
    (mapEquiv e : PontryaginDual B →ₜ* PontryaginDual A) = map (e : A →ₜ* B) := rfl

/-- A transported character is evaluated by applying the source equivalence first. -/
@[simp] theorem mapEquiv_apply (e : A ≃ₜ* B) (χ : PontryaginDual B) (a : A) :
    mapEquiv e χ a = χ (e a) := rfl

/-- Inverse dual transport is precomposition by the inverse equivalence. -/
@[simp] theorem mapEquiv_symm_apply (e : A ≃ₜ* B) (ψ : PontryaginDual A) (b : B) :
    (mapEquiv e).symm ψ b = ψ (e.symm b) := rfl

/-- Transport along the inverse equivalence is inverse dual transport. -/
@[simp] theorem mapEquiv_symm (e : A ≃ₜ* B) :
    mapEquiv e.symm = (mapEquiv e).symm := rfl

variable (A) in
/-- The identity equivalence induces the identity equivalence of the dual. -/
@[simp] theorem mapEquiv_refl :
    mapEquiv (ContinuousMulEquiv.refl A) = ContinuousMulEquiv.refl (PontryaginDual A) := by
  refine ContinuousMulEquiv.ext fun χ => PontryaginDual.ext fun a => ?_
  rfl

universe w

/-- Dual transport reverses the order of composition of equivalences. -/
theorem mapEquiv_trans {C : Type w} [Monoid C] [TopologicalSpace C]
    (e : A ≃ₜ* B) (f : B ≃ₜ* C) :
    mapEquiv (e.trans f) = (mapEquiv f).trans (mapEquiv e) := by
  refine ContinuousMulEquiv.ext fun χ => PontryaginDual.ext fun a => ?_
  rfl

end MapEquiv

/-- The canonical continuous homomorphism into the Pontryagin bidual, sending
`a` to the character `χ ↦ χ a`. The locally compact pair hypothesis supplies
joint evaluation on the original monoid; no local compactness of its dual is needed. -/
noncomputable def eval (A : Type u) [Monoid A] [TopologicalSpace A] [LocallyCompactPair A Circle] :
    A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun a :=
    { toFun := fun χ => χ a
      map_one' := one_apply a
      map_mul' := fun χ ψ => ContinuousMonoidHom.mul_apply χ ψ a
      continuous_toFun := continuous_eval_const (F := A →ₜ* Circle) a }
  map_one' := PontryaginDual.ext fun χ => _root_.map_one χ
  map_mul' := fun a b => PontryaginDual.ext fun χ => _root_.map_mul χ a b
  continuous_toFun := ContinuousMonoidHom.continuous_of_continuous_uncurry _
    (continuous_snd.eval (F := A →ₜ* Circle) continuous_fst)

variable {A : Type u} [Monoid A] [TopologicalSpace A] [LocallyCompactPair A Circle]

/-- Evaluating the bidual character associated to `a` at `χ` gives `χ a`. -/
@[simp] theorem eval_apply (a : A) (χ : PontryaginDual A) : eval A a χ = χ a := rfl

/-- Canonical bidual evaluation commutes with continuous monoid homomorphisms
and their twice-contravariant Pontryagin dual maps. -/
theorem eval_naturality {B : Type v} [Monoid B] [TopologicalSpace B]
    [LocallyCompactPair B Circle] (f : A →ₜ* B) :
    (map (map f)).comp (eval A) = (eval B).comp f := by
  refine ContinuousMonoidHom.ext fun a => PontryaginDual.ext fun χ => ?_
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, map_apply, eval_apply]

/-- Evaluation on the Pontryagin dual is a section of the dual of evaluation. -/
theorem map_eval_comp_eval [LocallyCompactPair (PontryaginDual A) Circle] :
    (map (eval A)).comp (eval (PontryaginDual A)) =
      ContinuousMonoidHom.id (PontryaginDual A) := by
  refine ContinuousMonoidHom.ext fun χ => PontryaginDual.ext fun a => ?_
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, map_apply, eval_apply,
    ContinuousMonoidHom.coe_id, id_eq]

end PontryaginDual
