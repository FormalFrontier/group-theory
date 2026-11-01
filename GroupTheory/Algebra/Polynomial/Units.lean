/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Regular.Defs
import GroupTheory.Algebra.IsAddUnit
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# Left inverses and unit images of polynomial roots

A multiplication-preserving map `μ : E →ₙ* T` to an arbitrary monoid sends a
polynomial root to an element with a left inverse if the image of the mapped
constant coefficient has a supplied left inverse. Preservation of one need not be
supplied: it follows from this constant-coefficient hypothesis. At such a root,
`μ x` is a unit if and only if right multiplication by `μ x` is injective
(`IsRightRegular (μ x)`). A left inverse alone need not give a unit.

In particular, a unit mapped constant coefficient suffices for a left inverse. For
a commutative target monoid, the unit-constant corollary gives a unit image.
Specializing the unit-constant result to the identity map gives a left inverse for
the root itself, without coefficient centrality. In this raw specialization, the
hypotheses force the evaluation semiring to admit a ring structure, even though no
`Ring` instance is required; the generic mapped result allows genuinely nonring
evaluation semirings.
-/

@[expose] public section

universe u v w

private theorem eval₂_constant_add_divX_mul_eq_zero {D : Type u} {E : Type v}
    [Semiring D] [Semiring E] (f : D →+* E) (p : Polynomial D) (x : E)
    (hroot : p.eval₂ f x = 0) :
    f (p.coeff 0) + p.divX.eval₂ f x * x = 0 := by
  have hsplit := congrArg (fun q : Polynomial D => q.eval₂ f x)
    (Polynomial.divX_mul_X_add p)
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
    hroot, add_comm] using hsplit

/-- The root decomposition gives a square identity before applying a multiplicative map. -/
private theorem eval₂_constant_square_eq
    {D : Type u} {E : Type v} [Semiring D] [Semiring E]
    (f : D →+* E) (p : Polynomial D) (x : E)
    (hroot : p.eval₂ f x = 0) :
    f (p.coeff 0) * f (p.coeff 0) =
      (p.divX.eval₂ f x * x) * (p.divX.eval₂ f x * x) := by
  exact mul_self_eq_mul_self_of_add_eq_zero
    (eval₂_constant_add_divX_mul_eq_zero f p x hroot)

namespace MulHom

/-- A multiplication-preserving map sends an evaluation root to an element with a
left inverse when a left inverse is supplied for the image of the mapped constant
coefficient. Preservation of one need not be supplied: it follows from this
constant-coefficient hypothesis. The target need only be a monoid, and no addition
or zero preservation, semiring commutativity or coefficient centrality is required.
The image is a unit exactly when right multiplication by it is injective; a left
inverse alone need not give a unit. -/
theorem exists_mul_apply_eq_one_of_eval₂_eq_zero_of_mul_coeff_zero_eq_one
    {R : Type u} {E : Type v} {T : Type w}
    [Semiring R] [Semiring E] [Monoid T]
    (μ : E →ₙ* T) (φ : R →+* E) (p : Polynomial R) (x : E)
    (l : T) (hleft : l * μ (φ (p.coeff 0)) = 1)
    (hroot : p.eval₂ φ x = 0) :
    ∃ y : T, y * μ x = 1 := by
  let b := p.divX.eval₂ φ x
  let A := μ (φ (p.coeff 0))
  let B := μ b
  let X := μ x
  have hsquare : A * A = (B * X) * (B * X) := by
    simpa only [map_mul] using
      congrArg μ (eval₂_constant_square_eq φ p x hroot)
  -- Use the supplied left inverse twice without commuting factors.
  refine ⟨(l * l) * ((B * X) * B), ?_⟩
  calc
    ((l * l) * ((B * X) * B)) * X =
        (l * l) * ((B * X) * (B * X)) := by
      simp only [mul_assoc]
    _ = (l * l) * (A * A) := by rw [← hsquare]
    _ = l * (l * A) * A := by simp only [mul_assoc]
    _ = 1 := by rw [hleft, mul_one, hleft]

/-- At an evaluation root, a multiplication-preserving map has a unit image exactly
when right multiplication by that image is injective, provided a left inverse is
supplied for the image of the mapped constant coefficient. Preservation of one is
not an input; it follows from this constant-coefficient hypothesis. Mathlib's
characterization of units by bijective right multiplication supplies both
implications. -/
theorem isUnit_apply_iff_isRightRegular_of_eval₂_eq_zero
    {R : Type u} {E : Type v} {T : Type w}
    [Semiring R] [Semiring E] [Monoid T]
    (μ : E →ₙ* T) (φ : R →+* E) (p : Polynomial R) (x : E)
    (l : T) (hleft : l * μ (φ (p.coeff 0)) = 1)
    (hroot : p.eval₂ φ x = 0) :
    IsUnit (μ x) ↔ IsRightRegular (μ x) := by
  constructor
  · intro hunit
    exact (IsUnit.isUnit_iff_mulRight_bijective.mp hunit).1
  · intro hregular
    obtain ⟨b, hb⟩ :=
      exists_mul_apply_eq_one_of_eval₂_eq_zero_of_mul_coeff_zero_eq_one
        μ φ p x l hleft hroot
    apply IsUnit.isUnit_iff_mulRight_bijective.mpr
    refine ⟨hregular, ?_⟩
    intro t
    refine ⟨t * b, ?_⟩
    calc
      (t * b) * μ x = t * (b * μ x) := mul_assoc _ _ _
      _ = t := by rw [hb, mul_one]

end MulHom

namespace MonoidHom

/-- A multiplicative image of an evaluation root has a left inverse if a left
inverse is supplied for the image of the mapped constant coefficient. The target
need only be a monoid. The map need not preserve addition or zero, and neither
semiring needs to be commutative. No coefficient centrality is required. -/
theorem exists_mul_apply_eq_one_of_eval₂_eq_zero_of_mul_coeff_zero_eq_one
    {R : Type u} {E : Type v} {T : Type w}
    [Semiring R] [Semiring E] [Monoid T]
    (μ : E →* T) (φ : R →+* E) (p : Polynomial R) (x : E)
    (l : T) (hleft : l * μ (φ (p.coeff 0)) = 1)
    (hroot : p.eval₂ φ x = 0) :
    ∃ y : T, y * μ x = 1 := by
  exact MulHom.exists_mul_apply_eq_one_of_eval₂_eq_zero_of_mul_coeff_zero_eq_one
    μ.toMulHom φ p x l hleft hroot

/-- A multiplicative image of an evaluation root has a left inverse if the image
of the mapped constant coefficient is a unit. The target need only be a monoid:
neither addition nor zero preservation is required of the map, and neither semiring
needs to be commutative. -/
theorem exists_mul_apply_eq_one_of_eval₂_eq_zero
    {D : Type u} {E : Type v} {T : Type w}
    [Semiring D] [Semiring E] [Monoid T]
    (μ : E →* T) (f : D →+* E) (p : Polynomial D) (x : E)
    (hconstant : IsUnit (μ (f (p.coeff 0))))
    (hroot : p.eval₂ f x = 0) :
    ∃ y : T, y * μ x = 1 := by
  obtain ⟨u, hu⟩ := hconstant
  let v : T := u.inv
  have hv : v * μ (f (p.coeff 0)) = 1 := by
    simpa only [v, ← hu] using u.inv_val
  exact exists_mul_apply_eq_one_of_eval₂_eq_zero_of_mul_coeff_zero_eq_one
    μ f p x v hv hroot

/-- A multiplicative map to a commutative monoid sends an evaluation root to a unit
when the image of the mapped constant coefficient is a unit. Neither the evaluation
semiring nor the coefficient semiring needs to be commutative. -/
theorem isUnit_apply_of_eval₂_eq_zero
    {D : Type u} {E : Type v} {T : Type w}
    [Semiring D] [Semiring E] [CommMonoid T]
    (φ : E →* T) (f : D →+* E) (p : Polynomial D) (x : E)
    (hconstant : IsUnit (φ (f (p.coeff 0))))
    (hroot : p.eval₂ f x = 0) :
    IsUnit (φ x) := by
  have hproduct : IsUnit (φ (p.divX.eval₂ f x * x)) :=
    (MulHomClass.isUnit_apply_iff_of_add_eq_zero φ
      (eval₂_constant_add_divX_mul_eq_zero f p x hroot)).mp hconstant
  rw [map_mul] at hproduct
  exact isUnit_of_mul_isUnit_right hproduct

end MonoidHom

namespace Polynomial

/-- An evaluation root has a left inverse if the mapped constant coefficient is a
unit. No coefficient centrality is needed. Although only a `Semiring S` instance is
required, the hypotheses force `S` to admit a ring structure; they do not give
genuinely nonring examples. -/
theorem exists_mul_eq_one_of_eval₂_eq_zero
    {R : Type u} {S : Type v}
    [Semiring R] [Semiring S]
    (φ : R →+* S) (p : Polynomial R) (x : S)
    (hconstant : IsUnit (φ (p.coeff 0)))
    (hroot : p.eval₂ φ x = 0) :
    ∃ y : S, y * x = 1 := by
  exact MonoidHom.exists_mul_apply_eq_one_of_eval₂_eq_zero
    (MonoidHom.id S) φ p x hconstant hroot

end Polynomial
