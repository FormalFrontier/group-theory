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
universal property does not assert bidual reflexivity or duality for infinite products.

## Main definitions

* `PontryaginDual.prodEquiv`: restriction to the two factors as a continuous
  multiplicative equivalence.

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

end PontryaginDual
