/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateSupportMap
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.UnitsFiniteCoordinates

/-!
# Coordinate support of unit lifts

The canonical lift to units preserves coordinate multiplication support.
-/

@[expose] public section

universe u v w

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, Group (G i)] [Monoid D]

/-- Lifting a homomorphism to units preserves its coordinate multiplication support. -/
@[simp]
theorem coordinateMulSupport_toHomUnits (f : (∀ i, G i) →* D) :
    f.toHomUnits.coordinateMulSupport = f.coordinateMulSupport := by
  have hval : (Units.coeHom D).comp f.toHomUnits = f := by
    ext x
    exact coe_toHomUnits f x
  simpa only [hval] using
    (coordinateMulSupport_comp_eq_of_injective f.toHomUnits (Units.coeHom D)
      (Units.coeHom_injective (M := D))).symm

end MonoidHom
