/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Unit lifts of finite-coordinate restrictions

The canonical unit lift commutes with finite-coordinate restriction.
-/

@[expose] public section

universe u v w

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, Group (G i)] [Monoid D]

/-- The canonical unit lift commutes with finite-coordinate restriction. -/
@[simp]
theorem toHomUnits_finiteCoordinateFactor (f : (∀ i, G i) →* D) (s : Finset ι) :
    (f.finiteCoordinateFactor s).toHomUnits = (f.toHomUnits).finiteCoordinateFactor s := by
  ext x
  simp only [coe_toHomUnits, finiteCoordinateFactor_apply]

end MonoidHom
