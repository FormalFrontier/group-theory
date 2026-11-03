/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Continuous monoid homomorphisms into units

A continuous monoid homomorphism from a group lifts to the units of its target.
For the compact-open topologies this lift is a homeomorphism whenever the source
and target form a `LocallyCompactPair`. Only continuity of source inversion is
needed: neither source multiplication nor target multiplication is assumed continuous.

The constructions reuse Mathlib's `MonoidHom.toHomUnits`, the topology on units,
and the compact-open topology and continuity API for `ContinuousMonoidHom`.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G] [ContinuousInv G]
  [Monoid D] [TopologicalSpace D]

/-- Lift a continuous monoid homomorphism from a group to the units of its target. -/
def toHomUnits (f : G →ₜ* D) : G →ₜ* Dˣ where
  toMonoidHom := f.toMonoidHom.toHomUnits
  continuous_toFun :=
    Continuous.of_coeHom_comp (f := f.toMonoidHom.toHomUnits) f.continuous


theorem toHomUnits_toMonoidHom (f : G →ₜ* D) :
    f.toHomUnits.toMonoidHom = f.toMonoidHom.toHomUnits := rfl

@[simp]
theorem toHomUnits_apply (f : G →ₜ* D) (g : G) : (f.toHomUnits g : D) = f g := rfl

/-- The value of the inverse unit is the value of the homomorphism at the inverse. -/
@[simp]
theorem toHomUnits_apply_inv (f : G →ₜ* D) (g : G) :
    (↑((f.toHomUnits g)⁻¹) : D) = f (g⁻¹) := by
  simpa only [map_inv] using (toHomUnits_apply f (g⁻¹))

/-- Lifting to units is continuous for the compact-open topologies. -/
theorem continuous_toHomUnits [LocallyCompactPair G D] :
    Continuous (toHomUnits : (G →ₜ* D) → (G →ₜ* Dˣ)) := by
  apply continuous_of_continuous_uncurry
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simpa only [Function.comp_def, Function.uncurry, toHomUnits_apply] using
      (continuous_fst.eval continuous_snd : Continuous (fun p : (G →ₜ* D) × G => p.1 p.2))
  · simpa only [Function.uncurry, toHomUnits_apply_inv] using
      (continuous_fst.eval continuous_snd.inv :
        Continuous (fun p : (G →ₜ* D) × G => p.1 (p.2⁻¹)))

/-- For a `LocallyCompactPair`, the compact-open homomorphism spaces into a monoid
and into its units are homeomorphic if the source is a group with continuous inversion. -/
def toHomUnitsHomeomorph [LocallyCompactPair G D] :
    (G →ₜ* D) ≃ₜ (G →ₜ* Dˣ) where
  toFun := toHomUnits
  invFun f :=
    ({ toMonoidHom := Units.coeHom D
       continuous_toFun := Units.continuous_val } : Dˣ →ₜ* D).comp f
  left_inv f := by
    apply ContinuousMonoidHom.ext
    intro g
    exact toHomUnits_apply f g
  right_inv f := by
    apply ContinuousMonoidHom.ext
    intro g
    apply Units.ext
    exact toHomUnits_apply _ g
  continuous_toFun := continuous_toHomUnits
  continuous_invFun := continuous_comp_right _

@[simp]
theorem toHomUnitsHomeomorph_apply [LocallyCompactPair G D] (f : G →ₜ* D) :
    toHomUnitsHomeomorph f = f.toHomUnits := rfl

theorem toHomUnitsHomeomorph_symm_apply [LocallyCompactPair G D] (f : G →ₜ* Dˣ) :
    toHomUnitsHomeomorph.symm f =
      ({ toMonoidHom := Units.coeHom D
         continuous_toFun := Units.continuous_val } : Dˣ →ₜ* D).comp f := rfl

@[simp]
theorem toHomUnitsHomeomorph_symm_apply_apply [LocallyCompactPair G D]
    (f : G →ₜ* Dˣ) (g : G) : (toHomUnitsHomeomorph.symm f) g = (f g : D) := rfl

@[simp]
theorem toHomUnits_toHomUnitsHomeomorph_symm [LocallyCompactPair G D] (f : G →ₜ* Dˣ) :
    (toHomUnitsHomeomorph.symm f).toHomUnits = f :=
  toHomUnitsHomeomorph.apply_symm_apply f

end ContinuousMonoidHom
