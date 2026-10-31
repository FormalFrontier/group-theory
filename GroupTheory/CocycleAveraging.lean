/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.NatInt

/-!
# Averaging crossed maps for finite groups

For a finite group acting by additive automorphisms on an additive commutative
group, bijective multiplication by the group order makes every crossed map
principal. The witness is the negative inverse-order multiple of its sum.

For a module over any semiring, a unit-valued group order is sufficient. The
inverse-order operator is then inverse-unit scalar multiplication; the given
additive group action need not be scalar-linear. The scalar bridges use Mathlib
`IsUnit.smul_bijective` and `Nat.cast_smul_eq_nsmul`, retaining the more general
bijective-nsmul averaging and additive-map naturality API.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87,
  Springer, 1982: the classical finite-group cohomology vanishing theorem.
* Mathlib group cohomology in degree one supplies `groupCohomology.IsCocycle₁`
  and its cocycle convention.
-/

public section

open scoped BigOperators

universe u v w r s

private theorem bijective_nsmul_of_isUnit_natCast
    {R : Type r} {A : Type v} [Semiring R] [AddCommMonoid A] [Module R A]
    (n : ℕ) (hn : IsUnit (n : R)) :
    Function.Bijective (fun a : A => n • a) := by
  simpa only [Nat.cast_smul_eq_nsmul] using hn.smul_bijective (β := A)

private theorem inverse_nsmul_eq_inv_smul
    {R : Type r} {A : Type v} [Semiring R] [AddCommMonoid A] [Module R A]
    (n : ℕ) (u : Rˣ) (hu : (u : R) = (n : R))
    (hN : Function.Bijective (fun a : A => n • a)) (a : A) :
    (Equiv.ofBijective _ hN).symm a = (↑(u⁻¹) : R) • a := by
  have he : n • (Equiv.ofBijective _ hN).symm a = a :=
    (Equiv.ofBijective _ hN).apply_symm_apply a
  apply hN.1
  change n • (Equiv.ofBijective _ hN).symm a = n • ((↑(u⁻¹) : R) • a)
  rw [he, ← Nat.cast_smul_eq_nsmul R, ← hu, smul_smul]
  simp


namespace AddMonoidHom

/-- Additive maps commute with the negative inverse-multiple sum. No action or crossed
relation is needed, and the index type need not be a group. -/
theorem map_neg_inverse_nsmul_sum
    {ι : Type u} {A : Type v} {B : Type w} [Fintype ι]
    [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (n : ℕ)
    (hA : Function.Bijective (fun a : A => n • a))
    (hB : Function.Bijective (fun b : B => n • b)) (z : ι → A) :
    f (-((Equiv.ofBijective _ hA).symm (∑ i, z i))) =
      -((Equiv.ofBijective _ hB).symm (∑ i, f (z i))) := by
  have heA (a : A) : n • (Equiv.ofBijective _ hA).symm a = a :=
    (Equiv.ofBijective _ hA).apply_symm_apply a
  have heB (b : B) : n • (Equiv.ofBijective _ hB).symm b = b :=
    (Equiv.ofBijective _ hB).apply_symm_apply b
  apply hB.1
  dsimp only
  rw [← map_nsmul, smul_neg, heA, map_neg, map_sum, smul_neg, heB]

/-- Additive maps commute with negative inverse-unit multiples of finite sums when
both units represent the same natural scalar, even over different semirings.
No coefficient-ring map, scalar linearity, or actions are needed. -/
theorem map_neg_inv_smul_sum
    {ι : Type u} {R : Type r} {S : Type s} {A : Type v} {B : Type w}
    [Fintype ι] [Semiring R] [Semiring S] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module S B] (f : A →+ B) (n : ℕ) (u : Rˣ) (v : Sˣ)
    (hu : (u : R) = (n : R)) (hv : (v : S) = (n : S)) (z : ι → A) :
    f (-((↑(u⁻¹) : R) • (∑ i, z i))) =
      -((↑(v⁻¹) : S) • (∑ i, f (z i))) := by
  have hnR : IsUnit (n : R) := hu ▸ u.isUnit
  have hnS : IsUnit (n : S) := hv ▸ v.isUnit
  have hA := bijective_nsmul_of_isUnit_natCast (A := A) n hnR
  have hB := bijective_nsmul_of_isUnit_natCast (A := B) n hnS
  simpa only [inverse_nsmul_eq_inv_smul n u hu hA,
    inverse_nsmul_eq_inv_smul n v hv hB] using
    f.map_neg_inverse_nsmul_sum n hA hB z

end AddMonoidHom

namespace groupCohomology

section Action
variable {G : Type u} {A : Type v}
variable [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The explicit negative inverse-order sum principalizes a crossed map for the
given action. This is the degree-one finite-group averaging theorem
(Brown, *Cohomology of Groups*). -/
theorem IsCocycle₁.eq_smul_sub_inverse_nsmul_sum [Fintype G]
    {z : G → A} (hz : IsCocycle₁ z)
    (hN : Function.Bijective (fun a : A => Nat.card G • a)) (g : G) :
    z g = g • (-((Equiv.ofBijective _ hN).symm (∑ h : G, z h))) -
      (-((Equiv.ofBijective _ hN).symm (∑ h : G, z h))) := by
  have hcross (g h : G) : z (g * h) = z g + g • z h := by
    simpa only [add_comm] using hz g h
  have he (a : A) : Nat.card G • (Equiv.ofBijective _ hN).symm a = a :=
    (Equiv.ofBijective _ hN).apply_symm_apply a
  have hsum : (∑ h : G, z h) = Nat.card G • z g + g • (∑ h : G, z h) := by
    calc
      _ = ∑ h : G, z (g * h) := (Equiv.sum_comp (Equiv.mulLeft g) z).symm
      _ = ∑ h : G, (z g + g • z h) := by simp only [hcross]
      _ = Nat.card G • z g + g • (∑ h : G, z h) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Nat.card_eq_fintype_card, Finset.smul_sum]
  have hv : Nat.card G • (-((Equiv.ofBijective _ hN).symm (∑ h : G, z h))) =
      -(∑ h : G, z h) := by rw [smul_neg, he]
  apply hN.1
  calc
    _ = (∑ h : G, z h) - g • (∑ h : G, z h) := eq_sub_of_add_eq hsum.symm
    _ = Nat.card G •
        (g • (-((Equiv.ofBijective _ hN).symm (∑ h : G, z h))) -
          (-((Equiv.ofBijective _ hN).symm (∑ h : G, z h)))) := by
      rw [nsmul_sub, smul_comm (Nat.card G) g, hv, smul_neg]
      abel

/-- A crossed map is principal whenever multiplication by the finite group order
is bijective on its coefficient group. -/
theorem IsCocycle₁.exists_eq_smul_sub [Finite G] {z : G → A} (hz : IsCocycle₁ z)
    (hN : Function.Bijective (fun a : A => Nat.card G • a)) :
    ∃ v : A, ∀ g : G, z g = g • v - v := by
  classical
  let _ := Fintype.ofFinite G
  exact ⟨-((Equiv.ofBijective _ hN).symm (∑ g : G, z g)),
    hz.eq_smul_sub_inverse_nsmul_sum hN⟩

/-- A unit-valued finite group order gives the explicit negative inverse-unit sum
principalizing a crossed map. The given additive action need not be scalar-linear.
This is the scalar-unit form of finite-group averaging (Brown, *Cohomology of Groups*). -/
theorem IsCocycle₁.eq_smul_sub_inv_smul_sum [Fintype G]
    {R : Type r} [Semiring R] [Module R A] {z : G → A}
    (hz : IsCocycle₁ z) (u : Rˣ) (hu : (u : R) = (Nat.card G : R)) (g : G) :
    z g = g • (-((↑(u⁻¹) : R) • (∑ h : G, z h))) -
      (-((↑(u⁻¹) : R) • (∑ h : G, z h))) := by
  have hn : IsUnit (Nat.card G : R) := hu ▸ u.isUnit
  have hN := bijective_nsmul_of_isUnit_natCast (A := A) (Nat.card G) hn
  simpa only [inverse_nsmul_eq_inv_smul (Nat.card G) u hu hN] using
    hz.eq_smul_sub_inverse_nsmul_sum hN g

/-- Every crossed map for a finite group is principal when its order is a unit
in a semiring acting on the coefficient group. No scalar/action compatibility is needed. -/
theorem IsCocycle₁.exists_eq_smul_sub_of_isUnit_card [Finite G]
    {R : Type r} [Semiring R] [Module R A] {z : G → A}
    (hz : IsCocycle₁ z) (hn : IsUnit (Nat.card G : R)) :
    ∃ v : A, ∀ g : G, z g = g • v - v := by
  exact hz.exists_eq_smul_sub
    (bijective_nsmul_of_isUnit_natCast (A := A) (Nat.card G) hn)

end Action

end groupCohomology
