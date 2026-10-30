/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Orbits and stabilizer quotients

A discrete orbit is homeomorphic to the left-coset quotient by its stabilizer when
its orbit map is continuous. The orbit has its subtype topology, and the quotient
has its coinduced topology.

The construction promotes Mathlib's orbit–stabilizer equivalence without
changing its underlying maps.
-/

@[expose] public section

universe u v

namespace MulAction

private theorem continuous_orbitEquivQuotientStabilizer_symm
    (G : Type u) [Group G] [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [MulAction G X] (x : X)
    (hx : Continuous (fun g : G => g • x)) :
    Continuous (orbitEquivQuotientStabilizer G x).symm := by
  have h : Continuous (ofQuotientStabilizer G x) :=
    ((QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff
      (g := ofQuotientStabilizer G x)).mpr hx
  exact h.subtype_mk (ofQuotientStabilizer_mem_orbit G x)

/-- The canonical orbit–stabilizer homeomorphism for a discrete orbit. -/
noncomputable def orbitHomeomorphQuotientStabilizer
    (G : Type u) [Group G] [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [MulAction G X]
    (x : X) [DiscreteTopology (orbit G x)]
    (hx : Continuous (fun g : G => g • x)) :
    orbit G x ≃ₜ G ⧸ stabilizer G x where
  toEquiv := MulAction.orbitEquivQuotientStabilizer G x
  continuous_toFun := by
    let : DiscreteTopology (G ⧸ stabilizer G x) :=
      DiscreteTopology.of_continuous_injective
        (continuous_orbitEquivQuotientStabilizer_symm G x hx)
        (orbitEquivQuotientStabilizer G x).symm.injective
    exact (orbitEquivQuotientStabilizer G x).toHomeomorphOfDiscrete.continuous_toFun
  continuous_invFun := by exact continuous_orbitEquivQuotientStabilizer_symm G x hx

variable (G : Type u) [Group G] [TopologicalSpace G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X]
variable (x : X) [DiscreteTopology (orbit G x)]
variable (hx : Continuous (fun g : G => g • x))

/-- The underlying equivalence is the canonical orbit–stabilizer equivalence. -/
theorem orbitHomeomorphQuotientStabilizer_toEquiv :
    (orbitHomeomorphQuotientStabilizer G x hx).toEquiv =
      orbitEquivQuotientStabilizer G x := by rfl

/-- The inverse sends the left coset of `g` to the orbit point `g • x`. -/
theorem orbitHomeomorphQuotientStabilizer_symm_mk_coe (g : G) :
    ((orbitHomeomorphQuotientStabilizer G x hx).symm
      (QuotientGroup.mk g) : X) = g • x := by rfl

/-- The orbit point represented by `g` maps to the left coset of `g`. -/
theorem orbitHomeomorphQuotientStabilizer_apply_smul (g : G) :
    orbitHomeomorphQuotientStabilizer G x hx ⟨g • x, ⟨g, rfl⟩⟩ =
      (QuotientGroup.mk g : G ⧸ stabilizer G x) := by
  let e := orbitEquivQuotientStabilizer G x
  have hy : e.symm (QuotientGroup.mk g) =
      (⟨g • x, ⟨g, rfl⟩⟩ : orbit G x) :=
    Subtype.ext (orbitHomeomorphQuotientStabilizer_symm_mk_coe G x hx g)
  exact (congrArg e hy.symm).trans (e.right_inv _)

/-- The homeomorphism commutes with the canonical action on the orbit. -/
theorem orbitHomeomorphQuotientStabilizer_smul (g : G) (y : orbit G x) :
    orbitHomeomorphQuotientStabilizer G x hx (g • y) =
      g • orbitHomeomorphQuotientStabilizer G x hx y := by
  exact orbitEquivQuotientStabilizer_smul x g y

/-- The inverse homeomorphism commutes with the canonical quotient action. -/
theorem orbitHomeomorphQuotientStabilizer_symm_smul (g : G)
    (q : G ⧸ stabilizer G x) :
    (orbitHomeomorphQuotientStabilizer G x hx).symm (g • q) =
      g • (orbitHomeomorphQuotientStabilizer G x hx).symm q := by
  exact orbitEquivQuotientStabilizer_symm_smul x g q

end MulAction
