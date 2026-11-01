/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.ContinuousOn

/-!
# Continuous homomorphisms from the integers

Evaluation at `Multiplicative.ofAdd (1 : ℤ)` identifies the compact-open space
`Multiplicative ℤ →ₜ* E` with any topological group `E`. The inverse equips
Mathlib's `zpowersHom E e` with continuity from the discrete integer source.
Its value at `n` is `e ^ n.toAdd`.

`ContinuousMonoidHom.intEvalHomeomorph` does not require a commutative target.
For a commutative topological group, `ContinuousMonoidHom.intEvalEquiv` upgrades
the same homeomorphism to a continuous multiplicative equivalence for the
standard pointwise multiplication. Neither construction requires local
compactness or separation. In particular, `intEvalEquiv Circle` identifies
`PontryaginDual (Multiplicative ℤ)` with `Circle` when those types are imported.

The algebraic classification is `zpowersHom`, not a new integer-power
construction. Continuity of the inverse family follows from joint continuity
on a product with a discrete right factor, followed by compact-open currying.

## References

* Mathlib's `Data.Int.Cast.Lemmas` (Mario Carneiro), for the integer universal
  property `zpowersHom` and its commutative refinement `zpowersMulHom`.
* Mathlib's `Topology.Algebra.ContinuousMonoidHom` and
  `Topology.Algebra.Group.CompactOpen` (Thomas Browning and Nailin Guan),
  for continuous homomorphisms, fixed evaluation and compact-open currying.
* Mathlib's `Topology.CompactOpen` (Reid Barton), for the compact-open
  function-space topology and continuity of currying.
* Mathlib's `Topology.ContinuousOn` (Sébastien Gouëzel), for joint continuity
  with a discrete factor.
* Mathlib's `Topology.Algebra.Group.ZPow` (Johannes Hölzl, Mario Carneiro and
  Patrick Massot), for continuity of integer powers.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

section Group

variable (E : Type u) [Group E] [TopologicalSpace E] [IsTopologicalGroup E]

/-- Evaluation at the integer generator is a homeomorphism from the compact-open
space of continuous integer homomorphisms to a topological group. Its inverse
has underlying monoid homomorphism `zpowersHom E e`. -/
def intEvalHomeomorph : (Multiplicative ℤ →ₜ* E) ≃ₜ E where
  toFun χ := χ (Multiplicative.ofAdd (1 : ℤ))
  invFun e :=
    { toMonoidHom := zpowersHom E e
      continuous_toFun := continuous_of_discreteTopology }
  left_inv χ := by
    apply toMonoidHom_injective
    exact (zpowersHom E).apply_symm_apply χ.toMonoidHom
  right_inv e := (zpowersHom E).symm_apply_apply e
  continuous_toFun := continuous_eval_const _
  continuous_invFun := by
    refine continuous_of_continuous_uncurry _ ?_
    exact continuous_prod_of_discrete_right.mpr
      (fun n : Multiplicative ℤ => continuous_zpow n.toAdd)

/-- The integer evaluation homeomorphism evaluates at the generator. -/
@[simp]
theorem intEvalHomeomorph_apply (χ : Multiplicative ℤ →ₜ* E) :
    intEvalHomeomorph E χ = χ (Multiplicative.ofAdd (1 : ℤ)) := rfl

/-- The inverse integer evaluation homeomorphism takes integer powers. -/
@[simp]
theorem intEvalHomeomorph_symm_apply (e : E) (n : Multiplicative ℤ) :
    (intEvalHomeomorph E).symm e n = e ^ n.toAdd := rfl

/-- Forgetting continuity in the inverse recovers Mathlib's integer-power homomorphism. -/
@[simp]
theorem intEvalHomeomorph_symm_toMonoidHom (e : E) :
    ((intEvalHomeomorph E).symm e : Multiplicative ℤ →* E) = zpowersHom E e := rfl

variable {E} {F : Type v} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- Generator evaluation commutes with continuous target homomorphisms. -/
theorem intEvalHomeomorph_naturality (f : E →ₜ* F) (χ : Multiplicative ℤ →ₜ* E) :
    intEvalHomeomorph F (f.comp χ) = f (intEvalHomeomorph E χ) := rfl

/-- Taking the integer-power homomorphism commutes with continuous target homomorphisms. -/
theorem intEvalHomeomorph_symm_naturality (f : E →ₜ* F) (e : E) :
    (intEvalHomeomorph F).symm (f e) = f.comp ((intEvalHomeomorph E).symm e) := by
  apply ContinuousMonoidHom.ext
  intro n
  simpa only [intEvalHomeomorph_symm_apply, coe_comp, Function.comp_apply] using
    (map_zpow f e n.toAdd).symm

end Group

section CommGroup

variable (E : Type u) [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]

/-- For a commutative topological group, generator evaluation is a continuous
multiplicative equivalence. Its homeomorphism is `intEvalHomeomorph E`, and its
underlying algebra agrees with the inverse of Mathlib's `zpowersMulHom E`. -/
def intEvalEquiv : (Multiplicative ℤ →ₜ* E) ≃ₜ* E :=
  ContinuousMulEquiv.mk' (intEvalHomeomorph E) (fun _ _ => rfl)

/-- The multiplicative refinement retains the integer evaluation homeomorphism. -/
@[simp]
theorem intEvalEquiv_toHomeomorph :
    (intEvalEquiv E).toHomeomorph = intEvalHomeomorph E := rfl

/-- The multiplicative integer evaluation equivalence evaluates at the generator. -/
@[simp]
theorem intEvalEquiv_apply (χ : Multiplicative ℤ →ₜ* E) :
    intEvalEquiv E χ = χ (Multiplicative.ofAdd (1 : ℤ)) := rfl

/-- The inverse multiplicative integer evaluation equivalence takes integer powers. -/
@[simp]
theorem intEvalEquiv_symm_apply (e : E) (n : Multiplicative ℤ) :
    (intEvalEquiv E).symm e n = e ^ n.toAdd := rfl

/-- Forgetting continuity in the multiplicative inverse recovers `zpowersHom`. -/
@[simp]
theorem intEvalEquiv_symm_toMonoidHom (e : E) :
    ((intEvalEquiv E).symm e : Multiplicative ℤ →* E) = zpowersHom E e := rfl

/-- Generator evaluation agrees with Mathlib's commutative algebraic classifier
on the underlying monoid homomorphism. -/
theorem intEvalEquiv_apply_eq_zpowersMulHom_symm (χ : Multiplicative ℤ →ₜ* E) :
    intEvalEquiv E χ = (zpowersMulHom E).symm χ.toMonoidHom := rfl

/-- The inverse agrees with Mathlib's commutative integer-power classifier after
forgetting continuity. -/
theorem intEvalEquiv_symm_toMonoidHom_eq_zpowersMulHom (e : E) :
    ((intEvalEquiv E).symm e).toMonoidHom = zpowersMulHom E e := rfl

variable {E} {F : Type v} [CommGroup F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- Multiplicative generator evaluation commutes with continuous target homomorphisms. -/
theorem intEvalEquiv_naturality (f : E →ₜ* F) (χ : Multiplicative ℤ →ₜ* E) :
    intEvalEquiv F (f.comp χ) = f (intEvalEquiv E χ) := rfl

/-- The inverse multiplicative classifier commutes with continuous target homomorphisms. -/
theorem intEvalEquiv_symm_naturality (f : E →ₜ* F) (e : E) :
    (intEvalEquiv F).symm (f e) = f.comp ((intEvalEquiv E).symm e) :=
  intEvalHomeomorph_symm_naturality f e

end CommGroup

end ContinuousMonoidHom
