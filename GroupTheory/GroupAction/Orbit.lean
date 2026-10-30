/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.GroupAction.Quotient
public import GroupTheory.GroupAction.QuotientMap

/-!
# Equivariant maps on orbits

Equivariant functions restrict to maps between orbits. These maps commute with the
orbit-stabilizer equivalences and the quotient maps induced by stabilizer inclusions.
-/

@[expose] public section

universe u v w

namespace MulActionHom

section SMul

variable {M : Type u} {X : Type v} {Y : Type w} [SMul M X] [SMul M Y]

/-- An equivariant function sends an orbit into the orbit of the image. -/
theorem mapsTo_orbit (f : X →[M] Y) (x : X) :
    Set.MapsTo f (MulAction.orbit M x) (MulAction.orbit M (f x)) := by
  intro y hy
  rcases MulAction.mem_orbit_iff.mp hy with ⟨m, rfl⟩
  exact MulAction.mem_orbit_iff.mpr ⟨m, (f.map_smul m x).symm⟩

end SMul

section Monoid

variable {M : Type u} {X : Type v} {Y : Type w}
variable [Monoid M] [MulAction M X] [MulAction M Y]

/-- The equivariant restriction of a function to the orbit of a point. -/
def orbitMap (f : X →[M] Y) (x : X) :
    MulAction.orbit M x →[M] MulAction.orbit M (f x) where
  toFun := (f.mapsTo_orbit x).restrict f _ _
  map_smul' m z := by
    apply Subtype.ext
    simpa only [Set.MapsTo.val_restrict_apply, MulAction.orbit.coe_smul,
      id_eq] using f.map_smul m (z : X)

/-- The value of the restriction, as a point of the target orbit. -/
theorem orbitMap_apply (f : X →[M] Y) (x : X) (z : MulAction.orbit M x) :
    f.orbitMap x z = ⟨f z, f.mapsTo_orbit x z.property⟩ :=
  rfl

/-- The underlying value of the restriction is the original function value. -/
@[simp] theorem orbitMap_coe (f : X →[M] Y) (x : X) (z : MulAction.orbit M x) :
    (f.orbitMap x z : Y) = f z :=
  rfl

end Monoid

section Group

variable {G : Type u} {X : Type v} {Y : Type w}
variable [Group G] [MulAction G X] [MulAction G Y]

/-- The stabilizer of a point is contained in the stabilizer of its image. -/
theorem stabilizer_le (f : X →[G] Y) (x : X) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (f x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← f.map_smul g x, hg]

/-- The orbit-stabilizer equivalences commute with an equivariant function and the
quotient map induced by the inclusion of stabilizers. -/
theorem orbitEquivQuotientStabilizer_naturality (f : X →[G] Y) (x : X)
    (z : MulAction.orbit G x) :
    MulAction.orbitEquivQuotientStabilizer G (f x) (f.orbitMap x z) =
      quotientMapOfLE (f.stabilizer_le x)
        (MulAction.orbitEquivQuotientStabilizer G x z) := by
  obtain ⟨q, rfl⟩ := (MulAction.orbitEquivQuotientStabilizer G x).symm.surjective z
  refine Quotient.inductionOn' q ?_
  intro g
  apply (MulAction.orbitEquivQuotientStabilizer G (f x)).symm.injective
  apply Subtype.ext
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    orbitMap_coe, quotientMapOfLE_apply_mk,
    MulAction.orbitEquivQuotientStabilizer_symm_apply] using f.map_smul g x

end Group

end MulActionHom
