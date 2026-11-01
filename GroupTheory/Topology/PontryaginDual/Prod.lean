/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom
public import GroupTheory.Topology.PontryaginDual

/-!
# Characters of binary products

Restriction along the two factor inclusions identifies the Pontryagin dual of a
binary product with the product of the factor duals. The inverse sends `(χ, ψ)`
to the character `(a, b) ↦ χ a * ψ b`. This is the circle-valued specialization of
`ContinuousMonoidHom.coprodContinuousMulEquiv`, with the direction reversed.

The equivalence uses the entire existing character spaces with their compact-open
topologies. The source monoids need not be commutative, have continuous operations,
or satisfy local compactness or separation hypotheses. This binary-product
universal property alone does not assert bidual reflexivity or duality for infinite products.

Given canonical bidual equivalences of the factors, `prodEvalEquiv` constructs
canonical biduality of their product. Its forward map is evaluation and its inverse
is expressed using the supplied factor inverses and the product-dual equivalences.
The factor data supply the needed continuity, without additional source hypotheses.

## Main definitions

* `PontryaginDual.prodEquiv`: restriction to the two factors as a continuous
  multiplicative equivalence.
* `PontryaginDual.prodEvalEquiv`: canonical biduality of a binary product from
  canonical bidual equivalences of its factors.

## References

* Mathlib's coproduct and factor inclusions in `Topology.Algebra.ContinuousMonoidHom`,
  and the coproduct universal property in `Algebra.Group.Prod`.
* Mathlib's `Topology.Algebra.PontryaginDual`, for the compact-open character spaces
  and their contravariant maps.
-/

@[expose] public section

universe u v w z

namespace PontryaginDual

variable (A : Type u) (B : Type v)
variable [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

/-- Restriction identifies the compact-open dual of a binary product with the
product of its compact-open duals. The inverse is the coproduct of characters. -/
noncomputable def prodEquiv :
    PontryaginDual (A × B) ≃ₜ* (PontryaginDual A × PontryaginDual B) :=
  (ContinuousMonoidHom.coprodContinuousMulEquiv A B Circle).symm

/-- The product-dual equivalence restricts a character to each factor. -/
@[simp]
theorem prodEquiv_apply (χ : PontryaginDual (A × B)) :
    prodEquiv A B χ =
      (map (ContinuousMonoidHom.inl A B) χ, map (ContinuousMonoidHom.inr A B) χ) := rfl

/-- The inverse product-dual equivalence is the coproduct of characters. -/
@[simp]
theorem prodEquiv_symm_apply (χ : PontryaginDual A × PontryaginDual B) :
    (prodEquiv A B).symm χ = χ.1.coprod χ.2 := rfl

/-- The character reconstructed from a pair multiplies their values. -/
theorem prodEquiv_symm_apply_apply (χ : PontryaginDual A × PontryaginDual B)
    (a : A) (b : B) :
    (prodEquiv A B).symm χ (a, b) = χ.1 a * χ.2 b := rfl

variable {A B}

/-- Characters on a product are determined by their restrictions to the two factors. -/
theorem prod_ext {χ ψ : PontryaginDual (A × B)}
    (hinl : map (ContinuousMonoidHom.inl A B) χ = map (ContinuousMonoidHom.inl A B) ψ)
    (hinr : map (ContinuousMonoidHom.inr A B) χ = map (ContinuousMonoidHom.inr A B) ψ) :
    χ = ψ := by
  apply (prodEquiv A B).injective
  simpa only [prodEquiv_apply] using Prod.ext hinl hinr

/-- Restriction to the factors commutes with the contravariant character maps
induced by a product of continuous monoid homomorphisms. -/
theorem prodEquiv_naturality {C : Type w} {D : Type z}
    [Monoid C] [Monoid D] [TopologicalSpace C] [TopologicalSpace D]
    (f : A →ₜ* C) (g : B →ₜ* D) :
    (prodEquiv A B : PontryaginDual (A × B) →ₜ* (PontryaginDual A × PontryaginDual B)).comp
        (map (f.prodMap g)) =
      ((map f).prodMap (map g)).comp
        (prodEquiv C D : PontryaginDual (C × D) →ₜ* (PontryaginDual C × PontryaginDual D)) := by
  refine ContinuousMonoidHom.ext fun χ => ?_
  simp only [ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_coe, Function.comp_apply,
    prodEquiv_apply, ContinuousMonoidHom.prodMap_apply]
  apply Prod.ext
  · apply PontryaginDual.ext
    intro a
    simp only [map_apply, ContinuousMonoidHom.prodMap_apply,
      ContinuousMonoidHom.inl_apply, _root_.map_one]
  · apply PontryaginDual.ext
    intro b
    simp only [map_apply, ContinuousMonoidHom.prodMap_apply,
      ContinuousMonoidHom.inr_apply, _root_.map_one]

section ProdEvalEquiv

private theorem prodEvalEquiv_evalHom
    (eA : A ≃ₜ* PontryaginDual (PontryaginDual A))
    (eB : B ≃ₜ* PontryaginDual (PontryaginDual B))
    (hA : ∀ (a : A) (χ : PontryaginDual A), eA a χ = χ a)
    (hB : ∀ (b : B) (ψ : PontryaginDual B), eB b ψ = ψ b)
    (a : A) (b : B) :
    (mapEquiv (prodEquiv A B).symm).trans
        (prodEquiv (PontryaginDual A) (PontryaginDual B))
        (evalHom (A × B) (a, b)) = (eA a, eB b) := by
  apply Prod.ext
  · apply PontryaginDual.ext
    intro χ
    simp only [ContinuousMulEquiv.trans_apply, prodEquiv_apply, map_apply,
      ContinuousMonoidHom.inl_apply, mapEquiv_apply, evalHom_apply,
      prodEquiv_symm_apply_apply, one_apply, mul_one, hA]
  · apply PontryaginDual.ext
    intro ψ
    simp only [ContinuousMulEquiv.trans_apply, prodEquiv_apply, map_apply,
      ContinuousMonoidHom.inr_apply, mapEquiv_apply, evalHom_apply,
      prodEquiv_symm_apply_apply, one_apply, one_mul, hB]

/-- Canonical biduality of a binary product from canonical bidual equivalences
of its factors. The forward map is evaluation; the inverse uses the supplied
factor inverses after the product-dual comparison. -/
noncomputable def prodEvalEquiv {A : Type u} {B : Type v} [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B]
    (eA : A ≃ₜ* PontryaginDual (PontryaginDual A))
    (eB : B ≃ₜ* PontryaginDual (PontryaginDual B))
    (hA : ∀ (a : A) (χ : PontryaginDual A), eA a χ = χ a)
    (hB : ∀ (b : B) (ψ : PontryaginDual B), eB b ψ = ψ b) :
    (A × B) ≃ₜ* PontryaginDual (PontryaginDual (A × B)) :=
  let q := (mapEquiv (prodEquiv A B).symm).trans
    (prodEquiv (PontryaginDual A) (PontryaginDual B))
  { toFun := evalHom (A × B)
    invFun Φ := (eA.symm ((q Φ).1), eB.symm ((q Φ).2))
    left_inv := by
      rintro ⟨a, b⟩
      have hq : q (evalHom (A × B) (a, b)) = (eA a, eB b) :=
        prodEvalEquiv_evalHom eA eB hA hB a b
      change (eA.symm ((q (evalHom (A × B) (a, b))).1),
        eB.symm ((q (evalHom (A × B) (a, b))).2)) = (a, b)
      rw [hq]
      exact Prod.ext (eA.symm_apply_apply a) (eB.symm_apply_apply b)
    right_inv := by
      intro Φ
      apply q.injective
      calc
        q (evalHom (A × B) (eA.symm ((q Φ).1), eB.symm ((q Φ).2))) =
            (eA (eA.symm ((q Φ).1)), eB (eB.symm ((q Φ).2))) :=
          prodEvalEquiv_evalHom eA eB hA hB _ _
        _ = q Φ := Prod.ext (eA.apply_symm_apply _) (eB.apply_symm_apply _)
    map_mul' := _root_.map_mul (evalHom (A × B))
    continuous_toFun := by
      have hc : Continuous fun x : A × B => q.symm (eA x.1, eB x.2) :=
        q.symm.continuous.comp
          ((eA.continuous.comp continuous_fst).prodMk
            (eB.continuous.comp continuous_snd))
      apply hc.congr
      rintro ⟨a, b⟩
      rw [← prodEvalEquiv_evalHom eA eB hA hB a b]
      exact q.symm_apply_apply _
    continuous_invFun := by
      exact (eA.symm.continuous.comp (continuous_fst.comp q.continuous)).prodMk
        (eB.symm.continuous.comp (continuous_snd.comp q.continuous)) }

variable (eA : A ≃ₜ* PontryaginDual (PontryaginDual A))
  (eB : B ≃ₜ* PontryaginDual (PontryaginDual B))
  (hA : ∀ (a : A) (χ : PontryaginDual A), eA a χ = χ a)
  (hB : ∀ (b : B) (ψ : PontryaginDual B), eB b ψ = ψ b)

/-- Product biduality coerces to the canonical evaluation homomorphism. -/
@[simp] theorem coe_prodEvalEquiv :
    (prodEvalEquiv eA eB hA hB :
      (A × B) →* PontryaginDual (PontryaginDual (A × B))) = evalHom (A × B) := rfl

/-- The algebraic homomorphism underlying product biduality is canonical evaluation. -/
theorem prodEvalEquiv_toMonoidHom :
    (prodEvalEquiv eA eB hA hB :
      (A × B) →ₜ* PontryaginDual (PontryaginDual (A × B))).toMonoidHom =
        evalHom (A × B) := rfl

/-- Product biduality evaluates each character at the given pair. -/
theorem prodEvalEquiv_apply (a : A) (b : B) (χ : PontryaginDual (A × B)) :
    prodEvalEquiv eA eB hA hB (a, b) χ = χ (a, b) := rfl

/-- The inverse of product biduality uses the two supplied inverses after
contravariant transport and restriction to the dual factors. -/
theorem prodEvalEquiv_symm_apply (Φ : PontryaginDual (PontryaginDual (A × B))) :
    (prodEvalEquiv eA eB hA hB).symm Φ =
      (eA.symm (((mapEquiv (prodEquiv A B).symm).trans
          (prodEquiv (PontryaginDual A) (PontryaginDual B)) Φ).1),
        eB.symm (((mapEquiv (prodEquiv A B).symm).trans
          (prodEquiv (PontryaginDual A) (PontryaginDual B)) Φ).2)) := rfl

/-- When continuous evaluation is bundled using a locally compact pair on the
product, it is the forward continuous homomorphism of product biduality. -/
theorem prodEvalEquiv_toContinuousMonoidHom [LocallyCompactPair (A × B) Circle] :
    (prodEvalEquiv eA eB hA hB :
      (A × B) →ₜ* PontryaginDual (PontryaginDual (A × B))) = eval (A × B) := rfl

end ProdEvalEquiv

end PontryaginDual
