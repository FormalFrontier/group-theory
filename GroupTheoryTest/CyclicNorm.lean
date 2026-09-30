module

public import GroupTheory.CyclicNorm
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

namespace GroupTheoryTest.CyclicNorm

open Finset

universe u v

example {A : Type u} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)
    (hm : 0 < m) (hperiod : sigma ^ m = 1)
    (hinj : Function.Injective (nsmulAddMonoidHom (α := A) m))
    (hlift : ∀ a : A, sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range →
      ∃ z : A, sigma z = z ∧ a - z ∈ (nsmulAddMonoidHom (α := A) m).range) :
    (∑ i ∈ range m, sigma ^ i).ker = (1 - sigma).range :=
  AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinj hlift

example {A : Type u} [AddCommGroup A] :
    (∑ i ∈ range 1, (1 : AddMonoid.End A) ^ i).ker =
      ((1 : AddMonoid.End A) - 1).range := by
  apply AddMonoid.End.cyclicNorm_ker_eq_one_sub_range (1 : AddMonoid.End A) 1
    (by decide) (by simp)
  · intro a b hab
    simpa using hab
  · intro a _
    exact ⟨a, by simp, by simp⟩

example {A : Type u} [AddCommGroup A] [Subsingleton A] (sigma : AddMonoid.End A)
    (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ range m, sigma ^ i).ker = (1 - sigma).range := by
  apply AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm
    (by ext a; exact Subsingleton.elim _ _)
  · intro a b _
    exact Subsingleton.elim _ _
  · intro a _
    exact ⟨a, Subsingleton.elim _ _, by simp⟩

example {A : Type u} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)
    (hm : 0 < m) (hperiod : sigma ^ m = 1)
    (hbij : Function.Bijective (nsmulAddMonoidHom (α := A) m)) :
    (∑ i ∈ range m, sigma ^ i).ker = (1 - sigma).range := by
  apply AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hbij.1
  intro a _
  exact ⟨0, map_zero sigma, by simpa using hbij.2 a⟩

example {A : Type u} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)
    (hm : 0 < m) (hperiod : sigma ^ m = 1)
    (hinj : Function.Injective (nsmulAddMonoidHom (α := A) m))
    (hlift : ∀ a : A, sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range →
      ∃ z : A, sigma z = z ∧ a - z ∈ (nsmulAddMonoidHom (α := A) m).range)
    {B : Type v} [AddCommGroup B] (restriction : B →+ A) (transfer : A →+ B)
    (hrestriction : Function.Injective restriction)
    (htransfer : restriction.comp transfer = ∑ i ∈ range m, sigma ^ i) :
    transfer.ker = (1 - sigma).range := by
  rw [← AddMonoidHom.ker_comp_of_injective transfer restriction hrestriction,
    htransfer, AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinj hlift]

example {A : Type u} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)
    (hlift : ∀ a : A, sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range →
      ∃ z : A, sigma z = z ∧ a - z ∈ (nsmulAddMonoidHom (α := A) m).range)
    (a : A)
    (hclass : (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := A) m).range) (sigma a) =
      (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := A) m).range) a) :
    ∃ z : A, sigma z = z ∧
      (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := A) m).range) z =
        (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := A) m).range) a := by
  obtain ⟨z, hz, hdiff⟩ := hlift a (QuotientAddGroup.eq_iff_sub_mem.mp hclass)
  exact ⟨z, hz, (QuotientAddGroup.eq_iff_sub_mem.mpr hdiff).symm⟩

private def inducedOnQuotient {A : Type u} [AddCommGroup A]
    (sigma : AddMonoid.End A) (m : ℕ) :
    A ⧸ (nsmulAddMonoidHom (α := A) m).range →+
      A ⧸ (nsmulAddMonoidHom (α := A) m).range :=
  QuotientAddGroup.map _ _ sigma (by
    rintro a ⟨b, rfl⟩
    exact ⟨sigma b, (map_nsmul sigma m b).symm⟩)

example {A : Type u} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)
    (hlift : ∀ a : A, sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range →
      ∃ z : A, sigma z = z ∧ a - z ∈ (nsmulAddMonoidHom (α := A) m).range)
    (q : A ⧸ (nsmulAddMonoidHom (α := A) m).range)
    (hfixed : inducedOnQuotient sigma m q = q) :
    ∃ z : A, sigma z = z ∧
      (QuotientAddGroup.mk' (nsmulAddMonoidHom (α := A) m).range) z = q := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  have hclass : sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range :=
    QuotientAddGroup.eq_iff_sub_mem.mp (by exact hfixed)
  obtain ⟨z, hz, hdiff⟩ := hlift a hclass
  exact ⟨z, hz, (QuotientAddGroup.eq_iff_sub_mem.mpr hdiff).symm⟩

private def swapIntPair : AddMonoid.End (ℤ × ℤ) where
  toFun pair := (pair.2, pair.1)
  map_zero' := rfl
  map_add' _ _ := rfl

example : (∑ i ∈ range 2, swapIntPair ^ i).ker = (1 - swapIntPair).range := by
  apply AddMonoid.End.cyclicNorm_ker_eq_one_sub_range swapIntPair 2 (by decide)
  · apply AddMonoidHom.ext
    rintro ⟨first, second⟩
    change swapIntPair (swapIntPair (first, second)) = (first, second)
    rfl
  · exact AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree (by decide)
  · intro ⟨first, second⟩ hclass
    obtain ⟨⟨witness, other⟩, hcoordinate⟩ := hclass
    have hfirst : 2 • witness = second - first := by
      have h := congrArg Prod.fst hcoordinate
      change 2 • witness = second - first at h
      exact h
    refine ⟨(first, first), rfl, ⟨(0, witness), ?_⟩⟩
    apply Prod.ext
    · simp
    · simpa using hfirst

example : ((1, 0) : ℤ × ℤ) ∉ (nsmulAddMonoidHom (α := ℤ × ℤ) 2).range := by
  rintro ⟨⟨witness, other⟩, h⟩
  have hfirst := congrArg Prod.fst h
  change (2 : ℤ) * witness = 1 at hfirst
  omega

example : (∑ i ∈ range 2, (-(1 : AddMonoid.End (ZMod 3))) ^ i).ker =
    ((1 : AddMonoid.End (ZMod 3)) - -(1 : AddMonoid.End (ZMod 3))).range := by
  apply AddMonoid.End.cyclicNorm_ker_eq_one_sub_range
    (-(1 : AddMonoid.End (ZMod 3))) 2 (by decide)
  · simp [pow_two]
  · decide
  · intro a _
    have hsurj : Function.Surjective (nsmulAddMonoidHom (α := ZMod 3) 2) := by decide
    exact ⟨0, by simp, by simpa using hsurj a⟩

example : ¬ (∀ a : ℤ, (-(1 : AddMonoid.End ℤ)) a - a ∈
      (nsmulAddMonoidHom (α := ℤ) 2).range →
      ∃ z : ℤ, (-(1 : AddMonoid.End ℤ)) z = z ∧
        a - z ∈ (nsmulAddMonoidHom (α := ℤ) 2).range) := by
  intro hlift
  have hclass : (-(1 : AddMonoid.End ℤ)) 1 - 1 ∈
      (nsmulAddMonoidHom (α := ℤ) 2).range := by
    refine ⟨-1, ?_⟩
    decide
  obtain ⟨z, hz, ⟨witness, hw⟩⟩ := hlift 1 hclass
  have hzzero : z = 0 := by
    change -z = z at hz
    omega
  change (2 : ℤ) * witness = 1 - z at hw
  omega

example : (∑ i ∈ range 2, (-(1 : AddMonoid.End ℤ)) ^ i).ker ≠
    ((1 : AddMonoid.End ℤ) - -(1 : AddMonoid.End ℤ)).range := by
  intro heq
  have hnorm : (1 : ℤ) ∈ (∑ i ∈ range 2, (-(1 : AddMonoid.End ℤ)) ^ i).ker := by
    change (∑ i ∈ range 2, (-(1 : AddMonoid.End ℤ)) ^ i) 1 = 0
    simp [Finset.sum_range_succ]
  rw [heq] at hnorm
  obtain ⟨witness, hw⟩ := hnorm
  change witness - -witness = (1 : ℤ) at hw
  omega

example : ¬ Function.Injective (nsmulAddMonoidHom (α := ZMod 2) 2) := by
  intro hinj
  have heq : (0 : ZMod 2) = 1 := hinj (by decide)
  exact zero_ne_one heq

example : (∑ i ∈ range 2, (1 : AddMonoid.End (ZMod 2)) ^ i).ker ≠
    ((1 : AddMonoid.End (ZMod 2)) - 1).range := by
  intro heq
  have hnorm : (1 : ZMod 2) ∈
      (∑ i ∈ range 2, (1 : AddMonoid.End (ZMod 2)) ^ i).ker := by
    change (∑ i ∈ range 2, (1 : AddMonoid.End (ZMod 2)) ^ i) 1 = 0
    simp
    decide
  rw [heq] at hnorm
  obtain ⟨witness, hw⟩ := hnorm
  have : (1 : ZMod 2) = 0 := by
    calc
      1 = ((1 : AddMonoid.End (ZMod 2)) - 1) witness := hw.symm
      _ = 0 := by simp
  exact one_ne_zero this

end GroupTheoryTest.CyclicNorm
