/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Surjective nonunit scalars on finitely generated abelian groups

For `n ≥ 2`, surjectivity of the actual map `x ↦ n • x` on a finitely generated
abelian group forces finiteness and coprimality of `n` with the group cardinality.
The forward proof derives an integer annihilator by Nakayama's lemma, then
derives torsion and uses finite generation to obtain finiteness. Cauchy's theorem
and the scalar inverse give coprimality; the converse is already in mathlib.
-/

public section

namespace AddCommGroup

variable {A : Type*} [AddCommGroup A] [AddGroup.FG A] {n : ℕ}

private theorem exists_annihilator (hn : 2 ≤ n)
    (hsurj : Function.Surjective (fun x : A => n • x)) :
    ∃ d : ℤ, d ≠ 0 ∧ (∃ k : ℤ, d = 1 + (n : ℤ) * k) ∧ ∀ x : A, d • x = 0 := by
  let I : Ideal ℤ := Ideal.span {(n : ℤ)}
  have hfg : (⊤ : Submodule ℤ A).FG :=
    @Module.Finite.fg_top ℤ A _ _ _ (Module.Finite.iff_addGroup_fg.mpr inferInstance)
  have hle : (⊤ : Submodule ℤ A) ≤ I • ⊤ := by
    intro x _
    obtain ⟨y, hy⟩ := hsurj x
    have hxy : (n : ℤ) • y = x := by simpa using hy
    rw [← hxy]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_top)
  obtain ⟨d, hd, hzero⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hfg hle
  have hdiv : (n : ℤ) ∣ d - 1 := Ideal.mem_span_singleton.mp hd
  obtain ⟨k, hk⟩ := hdiv
  have hdk : d = 1 + (n : ℤ) * k := by omega
  have hdn : d ≠ 0 := by
    intro hz
    have hunit : (n : ℤ) ∣ (1 : ℤ) := by
      have : (n : ℤ) ∣ -(d - 1) := dvd_neg.mpr ⟨k, hk⟩
      simpa [hz] using this
    have hnat : n ∣ 1 := Int.natCast_dvd_natCast.mp hunit
    have hone : n = 1 := Nat.dvd_one.mp hnat
    omega
  exact ⟨d, hdn, ⟨k, hdk⟩, fun x => hzero x (Submodule.mem_top)⟩

/-- An actual surjective `n`-scalar map has a two-sided inverse given by one
integer scalar, uniformly for all elements. -/
theorem exists_zsmul_inverse_of_nsmul_surjective (hn : 2 ≤ n)
    (hsurj : Function.Surjective (fun x : A => n • x)) :
    ∃ k : ℤ, (∀ x : A, n • (k • x) = x) ∧ (∀ x : A, k • (n • x) = x) := by
  obtain ⟨d, _, ⟨k, hk⟩, hzero⟩ := exists_annihilator hn hsurj
  have hsum (x : A) : x + (n : ℤ) • (k • x) = 0 := by
    simpa only [hk, add_smul, one_smul, mul_smul] using hzero x
  refine ⟨-k, ?_, ?_⟩
  · intro x
    calc
      n • (-k • x) = -((n : ℤ) • (k • x)) := by
        rw [neg_smul, smul_neg, natCast_zsmul]
      _ = x := neg_eq_of_add_eq_zero_left (hsum x)
  · intro x
    calc
      (-k) • (n • x) = -((n : ℤ) • (k • x)) := by
        rw [neg_smul, natCast_zsmul, smul_comm]
      _ = x := neg_eq_of_add_eq_zero_left (hsum x)

/-- Surjectivity by a fixed natural scalar `n ≥ 2` on a finitely generated
abelian group forces finiteness and coprimality with the group order. -/
theorem finite_coprime_of_nsmul_surjective (hn : 2 ≤ n)
    (hsurj : Function.Surjective (fun x : A => n • x)) :
    Finite A ∧ Nat.Coprime n (Nat.card A) := by
  obtain ⟨d, hd, _, hzero⟩ := exists_annihilator hn hsurj
  have htorsion : IsAddTorsion A := by
    intro x
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨d, hd, hzero x⟩
  have hfinite : Finite A := AddCommGroup.finite_of_fg_isAddTorsion A htorsion
  obtain ⟨k, _, hinv⟩ := exists_zsmul_inverse_of_nsmul_surjective hn hsurj
  refine ⟨hfinite, Nat.coprime_of_dvd (fun p hp hpn hpc => ?_)⟩
  obtain ⟨x, hx⟩ := @exists_prime_addOrderOf_dvd_card' A _ hfinite p ⟨hp⟩ hpc
  have hnx : n • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by simpa [hx] using hpn)
  have hxzero : x = 0 := by simpa [hnx] using (hinv x).symm
  exact hp.ne_one (by simpa [hxzero] using hx.symm)

/-- For a finitely generated abelian group, the actual `n`-scalar map is
surjective exactly when the group is finite of cardinality coprime to `n`. -/
theorem nsmul_surjective_iff_finite_coprime (hn : 2 ≤ n) :
    Function.Surjective (fun x : A => n • x) ↔
      Finite A ∧ Nat.Coprime n (Nat.card A) := by
  constructor
  · exact finite_coprime_of_nsmul_surjective hn
  · rintro ⟨hfinite, hcoprime⟩
    exact (Nat.Coprime.nsmul_right_bijective hcoprime.symm).surjective

/-- The same criterion characterizes bijectivity of the actual scalar map. -/
theorem nsmul_bijective_iff_finite_coprime (hn : 2 ≤ n) :
    Function.Bijective (fun x : A => n • x) ↔
      Finite A ∧ Nat.Coprime n (Nat.card A) := by
  constructor
  · exact fun h => finite_coprime_of_nsmul_surjective hn h.surjective
  · rintro ⟨hfinite, hcoprime⟩
    exact Nat.Coprime.nsmul_right_bijective hcoprime.symm

end AddCommGroup
