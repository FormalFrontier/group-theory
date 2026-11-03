/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Units
import Mathlib.Topology.CompactOpen

/-!
# Unit valuation on spaces of continuous monoid homomorphisms

Postcomposition by unit valuation is continuous for the compact-open topology on
continuous monoid homomorphisms. The argument restricts Mathlib's
`ContinuousMap.continuous_postcomp` along the forgetful maps to continuous maps.
No compatibility of the target topology with multiplication is needed.

For a group with continuous inversion, valuation postcomposition is the two-sided
inverse of `ContinuousMonoidHom.toHomUnits`. Consequently the latter map is open.
This does not assert continuity of the unit-lifting map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace ContinuousMonoidHom

section Valuation

variable {A : Type u} {D : Type v}
  [Monoid A] [TopologicalSpace A] [Monoid D] [TopologicalSpace D]

/-- Postcomposition of a continuous unit-valued monoid homomorphism by unit valuation. -/
def compUnitsVal (f : A →ₜ* Dˣ) : A →ₜ* D :=
  ({ toMonoidHom := Units.coeHom D
     continuous_toFun := Units.continuous_val } : Dˣ →ₜ* D).comp f

/-- Valuation postcomposition takes the value of the unit at each argument. -/
@[simp]
theorem compUnitsVal_apply (f : A →ₜ* Dˣ) (a : A) :
    f.compUnitsVal a = (f a : D) := by
  exact Units.coeHom_apply (f a)

/-- Unit valuation induces a continuous map on compact-open homomorphism spaces. -/
theorem continuous_compUnitsVal :
    Continuous (compUnitsVal : (A →ₜ* Dˣ) → (A →ₜ* D)) := by
  let val : C(Dˣ, D) := ⟨(fun z => (z : D)), Units.continuous_val⟩
  have hforget : Continuous
      (toContinuousMap : (A →ₜ* Dˣ) → C(A, Dˣ)) := continuous_induced_dom
  have hpost : Continuous
      (fun f : A →ₜ* Dˣ => val.comp f.toContinuousMap) :=
    (ContinuousMap.continuous_postcomp val).comp hforget
  have heq :
      (fun f : A →ₜ* Dˣ => val.comp f.toContinuousMap) =
        (fun f : A →ₜ* Dˣ => f.compUnitsVal.toContinuousMap) := by
    funext f
    apply ContinuousMap.ext
    intro a
    exact (compUnitsVal_apply f a).symm
  rw [heq] at hpost
  exact continuous_induced_rng.2 hpost

end Valuation

section UnitLifting

variable {G : Type u} {D : Type v}
  [Group G] [TopologicalSpace G] [ContinuousInv G] [Monoid D] [TopologicalSpace D]

/-- Valuation postcomposition is a left inverse of the unit lift. -/
@[simp]
theorem compUnitsVal_toHomUnits (f : G →ₜ* D) :
    f.toHomUnits.compUnitsVal = f := by
  apply ContinuousMonoidHom.ext
  intro g
  simp only [compUnitsVal_apply, toHomUnits_apply]

/-- Valuation postcomposition is a right inverse of the unit lift. -/
@[simp]
theorem toHomUnits_compUnitsVal (h : G →ₜ* Dˣ) :
    h.compUnitsVal.toHomUnits = h := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  simp only [toHomUnits_apply, compUnitsVal_apply]

/-- Unit lifting is open because its inverse is continuous valuation postcomposition. -/
theorem isOpenMap_toHomUnits :
    IsOpenMap (toHomUnits : (G →ₜ* D) → (G →ₜ* Dˣ)) := by
  intro s hs
  have himage :
      (toHomUnits : (G →ₜ* D) → (G →ₜ* Dˣ)) '' s =
        (compUnitsVal : (G →ₜ* Dˣ) → (G →ₜ* D)) ⁻¹' s := by
    apply Set.ext
    intro h
    constructor
    · rintro ⟨f, hf, rfl⟩
      simpa only [Set.mem_preimage, compUnitsVal_toHomUnits] using hf
    · intro hh
      exact ⟨h.compUnitsVal, hh, toHomUnits_compUnitsVal h⟩
  rw [himage]
  exact hs.preimage continuous_compUnitsVal

end UnitLifting

end ContinuousMonoidHom
