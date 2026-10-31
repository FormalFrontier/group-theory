/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Averaging crossed maps for finite groups

For a finite group acting by additive automorphisms on an additive commutative
group, bijective multiplication by the group order makes every crossed map
principal. The witness is the negative inverse-order multiple of its sum.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87,
  Springer, 1982: the classical finite-group cohomology vanishing theorem.
* Mathlib group cohomology in degree one supplies `groupCohomology.IsCocycle₁`
  and its cocycle convention.
-/

public section

open scoped BigOperators

universe u v w

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

end Action

end groupCohomology
