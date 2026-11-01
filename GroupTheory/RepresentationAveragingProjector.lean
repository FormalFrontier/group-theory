/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import GroupTheory.RepresentationNorm
public import GroupTheory.RepresentationNormNaturality

/-!
# Normalized norm as a self-intertwiner

The norm of a finite-group representation is normalized by the inverse of
its numerical endomorphism. The resulting self-intertwiner projects onto
`Representation.fixedSubmodule`, naturally in intertwiners. Neither the
coefficient semiring nor the additive monoid needs to be a ring or group.

The value formulas allow every unit representing the group order and every
finite enumeration. The principal construction requires only `Finite`.

## References

The construction reuses Mathlib's representation norm and intertwining maps,
and GroupTheory's fixed submodule, norm on fixed vectors, and norm naturality.
-/

@[expose] public section

noncomputable section

universe uR uG uV uW

namespace Module.End

variable {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommMonoid V] [Module R V]

private theorem isUnit_natCast_of_isUnit (n : ℕ) (h : IsUnit (n : R)) :
    IsUnit (n : Module.End R V) := by
  rw [Module.End.isUnit_iff]
  have hb : Function.Bijective (fun v : V => (n : R) • v) := IsUnit.smul_bijective h
  convert hb using 1
  ext v
  simp only [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

/-- A unit numerical scalar cancels the inverse numerical endomorphism,
without a scalar module structure on the endomorphism semiring. -/
theorem natCast_smul_inverse_natCast_apply (n : ℕ) (h : IsUnit (n : R)) (v : V) :
    (n : R) • Ring.inverse (n : Module.End R V) v = v := by
  have hc := congrArg (fun f : Module.End R V => f v)
    (Ring.mul_inverse_cancel (n : Module.End R V) (isUnit_natCast_of_isUnit n h))
  change (n : Module.End R V) (Ring.inverse (n : Module.End R V) v) = v at hc
  simpa only [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul] using hc

/-- The inverse numerical endomorphism acts by the inverse of any coefficient
unit representing that number. This does not assert that arbitrary scalar
multiplication is coefficient-linear. -/
theorem inverse_natCast_apply (n : ℕ) (u : Rˣ) (hu : (u : R) = (n : R)) (v : V) :
    Ring.inverse (n : Module.End R V) v = (↑u⁻¹ : R) • v := by
  have h : IsUnit (n : R) := hu ▸ u.isUnit
  apply (IsUnit.smul_bijective h).1
  change (n : R) • Ring.inverse (n : Module.End R V) v = (n : R) • ((↑u⁻¹ : R) • v)
  rw [natCast_smul_inverse_natCast_apply n h, ← hu, ← mul_smul]
  simp

end Module.End

namespace Representation

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [Semiring R] [Group G] [Finite G] [AddCommMonoid V] [Module R V]

/-- The normalized norm of a representation, as a self-intertwiner.
The inverse is taken in the endomorphism semiring, so coefficients need not commute. -/
def averagingProjector (ρ : Representation R G V) (h : IsUnit (Nat.card G : R)) :
    IntertwiningMap ρ ρ := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toLinearMap := (Ring.inverse (Nat.card G : Module.End R V)).comp (norm ρ)
      isIntertwining' := fun g => LinearMap.ext fun v => ?_ }
  change Ring.inverse (Nat.card G : Module.End R V) (norm ρ (ρ g v)) =
    ρ g (Ring.inverse (Nat.card G : Module.End R V) (norm ρ v))
  rw [norm_self_apply]
  apply (IsUnit.smul_bijective h).1
  change (Nat.card G : R) • Ring.inverse (Nat.card G : Module.End R V) (norm ρ v) =
    (Nat.card G : R) • ρ g (Ring.inverse (Nat.card G : Module.End R V) (norm ρ v))
  rw [Module.End.natCast_smul_inverse_natCast_apply _ h, ← (ρ g).map_smul,
    Module.End.natCast_smul_inverse_natCast_apply _ h, self_norm_apply]

/-- The underlying coefficient-linear map is the inverse numerical
endomorphism composed with the representation norm. -/
theorem averagingProjector_toLinearMap (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) :
    (averagingProjector ρ h).toLinearMap =
      (Ring.inverse (Nat.card G : Module.End R V)).comp
        (@Representation.norm R G V _ _ (Fintype.ofFinite G) _ _ ρ) := rfl

/-- Evaluation in terms of the inverse numerical endomorphism. The scalar and
sum formulas below avoid exposing this implementation. -/
theorem averagingProjector_apply (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v =
      Ring.inverse (Nat.card G : Module.End R V)
        (@Representation.norm R G V _ _ (Fintype.ofFinite G) _ _ ρ v) := rfl

/-- Multiplying the mean by the group order recovers the norm. -/
theorem natCard_smul_averagingProjector (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    (Nat.card G : R) • averagingProjector ρ h v =
      @Representation.norm R G V _ _ (Fintype.ofFinite G) _ _ ρ v := by
  rw [averagingProjector_apply, Module.End.natCast_smul_inverse_natCast_apply _ h]

/-- Normalization is compatible with any supplied finite enumeration. -/
theorem natCard_smul_averagingProjector_fintype [Fintype G] (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    (Nat.card G : R) • averagingProjector ρ h v = norm ρ v := by
  rw [natCard_smul_averagingProjector]
  rw [show Fintype.ofFinite G = (inferInstance : Fintype G) from Subsingleton.elim _ _]

/-- The mean is independent of the proof that the group order is a unit. -/
theorem averagingProjector_eq (ρ : Representation R G V)
    (h h' : IsUnit (Nat.card G : R)) :
    averagingProjector ρ h = averagingProjector ρ h' := by
  ext v
  rfl

/-- Every unit representing the group order gives the same normalized norm. -/
theorem averagingProjector_apply_of_unit (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v = (↑u⁻¹ : R) •
      @Representation.norm R G V _ _ (Fintype.ofFinite G) _ _ ρ v := by
  rw [averagingProjector_apply, Module.End.inverse_natCast_apply _ u hu]

/-- The finite-only value formula, for every unit representing the order.
The displayed finite set is the canonical enumeration supplied by `Finite`. -/
theorem averagingProjector_apply_eq_sum (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v = (↑u⁻¹ : R) •
      ∑ g ∈ @Finset.univ G (Fintype.ofFinite G), ρ g v := by
  rw [averagingProjector_apply_of_unit ρ h u hu]
  simp [Representation.norm]

/-- The same mean is computed by any supplied finite enumeration, not just
`Fintype.ofFinite`. The principal constructor does not require that enumeration. -/
theorem averagingProjector_apply_eq_sum_fintype [Fintype G] (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v = (↑u⁻¹ : R) • ∑ g : G, ρ g v := by
  rw [averagingProjector_apply_eq_sum ρ h u hu]
  rw [show Fintype.ofFinite G = (inferInstance : Fintype G) from Subsingleton.elim _ _]

/-- The mean of any vector is fixed by the representation. -/
theorem averagingProjector_mem_fixedSubmodule (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v ∈ ρ.fixedSubmodule := by
  let : Fintype G := Fintype.ofFinite G
  rw [mem_fixedSubmodule]
  intro g
  apply (IsUnit.smul_bijective h).1
  change (Nat.card G : R) • ρ g (averagingProjector ρ h v) =
    (Nat.card G : R) • averagingProjector ρ h v
  rw [← (ρ g).map_smul, natCard_smul_averagingProjector, self_norm_apply]

/-- The mean restricts to the identity on the existing fixed submodule. -/
theorem averagingProjector_eq_self (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) {v : V} (hv : v ∈ ρ.fixedSubmodule) :
    averagingProjector ρ h v = v := by
  let : Fintype G := Fintype.ofFinite G
  apply (IsUnit.smul_bijective h).1
  change (Nat.card G : R) • averagingProjector ρ h v = (Nat.card G : R) • v
  rw [natCard_smul_averagingProjector]
  simpa only [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul] using
    norm_apply_coe_fixedSubmodule ρ ⟨v, hv⟩

/-- A vector is unchanged by averaging precisely when it is fixed. -/
@[simp]
theorem averagingProjector_eq_self_iff (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector ρ h v = v ↔ v ∈ ρ.fixedSubmodule := by
  constructor
  · intro hv
    rw [← hv]
    exact averagingProjector_mem_fixedSubmodule ρ h v
  · exact averagingProjector_eq_self ρ h

/-- Averaging a fixed-submodule element returns that element. -/
@[simp]
theorem averagingProjector_apply_coe_fixedSubmodule (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : ρ.fixedSubmodule) :
    averagingProjector ρ h (v : V) = v := averagingProjector_eq_self ρ h v.property

/-- Averaging twice is the same as averaging once. -/
@[simp]
theorem averagingProjector_apply_apply (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    averagingProjector ρ h (averagingProjector ρ h v) = averagingProjector ρ h v :=
  averagingProjector_eq_self ρ h (averagingProjector_mem_fixedSubmodule ρ h v)

/-- The normalized norm is an idempotent self-intertwiner. -/
@[simp]
theorem averagingProjector_comp_self (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) :
    (averagingProjector ρ h).comp (averagingProjector ρ h) = averagingProjector ρ h := by
  ext v
  exact averagingProjector_apply_apply ρ h v

/-- The coefficient-linear range of the mean is exactly the existing fixed submodule. -/
@[simp]
theorem range_averagingProjector (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) :
    (averagingProjector ρ h).toLinearMap.range = ρ.fixedSubmodule := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact averagingProjector_mem_fixedSubmodule ρ h w
  · intro hv
    exact ⟨v, averagingProjector_eq_self ρ h hv⟩

namespace IntertwiningMap

variable {W : Type uW} [AddCommMonoid W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Intertwiners commute with the means. This is the normalization of the
existing naturality theorem for the norm. -/
theorem averagingProjector_comm_apply (f : IntertwiningMap ρ σ)
    (h : IsUnit (Nat.card G : R)) (v : V) :
    f (averagingProjector ρ h v) = averagingProjector σ h (f v) := by
  let : Fintype G := Fintype.ofFinite G
  apply (IsUnit.smul_bijective h).1
  change (Nat.card G : R) • f.toLinearMap (averagingProjector ρ h v) =
    (Nat.card G : R) • averagingProjector σ h (f v)
  rw [← f.toLinearMap.map_smul, natCard_smul_averagingProjector,
    natCard_smul_averagingProjector]
  exact f.norm_comm_apply v

/-- Naturality as an equality of intertwiners. -/
theorem averagingProjector_comm (f : IntertwiningMap ρ σ)
    (h : IsUnit (Nat.card G : R)) :
    f.comp (averagingProjector ρ h) = (averagingProjector σ h).comp f := by
  ext v
  exact f.averagingProjector_comm_apply h v

end IntertwiningMap

/-- Among self-intertwiners, the mean is the unique retraction onto the fixed
vectors. Equivariance is essential: uniqueness among arbitrary coefficient-linear
retractions onto this submodule does not hold. -/
theorem eq_averagingProjector (ρ : Representation R G V)
    (h : IsUnit (Nat.card G : R)) (p : IntertwiningMap ρ ρ)
    (hp : ∀ v, p v ∈ ρ.fixedSubmodule)
    (hfix : ∀ v ∈ ρ.fixedSubmodule, p v = v) : p = averagingProjector ρ h := by
  ext v
  calc
    p v = averagingProjector ρ h (p v) := (averagingProjector_eq_self ρ h (hp v)).symm
    _ = p (averagingProjector ρ h v) := (p.averagingProjector_comm_apply h v).symm
    _ = averagingProjector ρ h v := hfix _ (averagingProjector_mem_fixedSubmodule ρ h v)

end Representation
