/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Evaluation into the Pontryagin bidual

For a monoid with a topology, evaluation at a point is a continuous circle-valued
character of its Pontryagin dual. When the monoid and the circle form a locally
compact pair, these characters assemble into a continuous homomorphism to the
bidual, equipped with its iterated compact-open topology.

The evaluation homomorphism is natural under continuous monoid homomorphisms.
If the dual and the circle also form a locally compact pair, evaluation on the
dual is a section of the dual of evaluation. This triangular identity does not
assert that evaluation on the original monoid is an isomorphism.

## Main definitions

* `PontryaginDual.eval`: the canonical continuous homomorphism into the bidual.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.10)–(1.1.11), for canonical bidual evaluation and its naturality.
* Mathlib's `Topology.Algebra.Group.CompactOpen` and `Topology.CompactOpen`,
  for compact-open evaluation and currying on the existing continuous homomorphism spaces.
* Mathlib's `MonoidHom.eval` and `AddChar.doubleDualEmb` are algebraic counterparts;
  `AddChar.doubleDualEquiv` in `Analysis.Fourier.FiniteAbelian.PontryaginDuality`
  gives finite-character biduality. Those abstract-character models are not
  substituted for the continuous characters or topologies used here.
-/

@[expose] public section

universe u v

namespace PontryaginDual

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
