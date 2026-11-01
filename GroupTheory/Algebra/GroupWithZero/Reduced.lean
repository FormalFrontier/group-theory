/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Zero products in reduced monoids with zero

In a reduced monoid with zero, replacing either factor of a product by a positive
natural power does not change whether the product is zero. The simp lemmas
`pow_mul_eq_zero_iff` and `mul_pow_eq_zero_iff` preserve the order of the factors;
commutativity and absence of zero divisors are not required.

The proofs use Mathlib's square-zero criterion `sq_eq_zero_iff`, upward propagation
`pow_mul_eq_zero_of_le`, and the reducedness and power APIs for `MulOpposite`.
When the other factor is one, these specialize to Mathlib's `pow_eq_zero_iff`.

`List.Perm.prod_eq_zero_iff` shows that permuting a list preserves whether its
product is zero, without asserting equality of the products.
-/

@[expose] public section

universe u

/-- In a reduced monoid with zero, reversing the factors preserves a zero product. -/
theorem IsReduced.mul_eq_zero_comm {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} : a * b = 0 ↔ b * a = 0 := by
  have reverse (a b : M) (hab : a * b = 0) : b * a = 0 := by
    apply sq_eq_zero_iff.mp
    calc
      (b * a) ^ 2 = b * (a * b) * a := by simp only [pow_two, mul_assoc]
      _ = 0 := by rw [hab, mul_zero, zero_mul]
  exact ⟨reverse a b, reverse b a⟩

/-- A positive power has the same right annihilators as the element itself in a
reduced monoid with zero. Positivity is essential: the zeroth power is one.
Reducedness is essential already with `b = 1` and a nonzero square-zero element. -/
@[simp]
theorem pow_mul_eq_zero_iff {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} {m : ℕ} (hm : m ≠ 0) : a ^ m * b = 0 ↔ a * b = 0 := by
  have square_step (c : M) (h : a ^ 2 * c = 0) : a * c = 0 := by
    -- Two square-zero tests remove the repeated factor without commuting it past `c`.
    have haca : a * c * a = 0 := sq_eq_zero_iff.mp <| by
      calc
        (a * c * a) ^ 2 = a * c * (a ^ 2 * c) * a := by
          simp only [pow_two, mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    apply sq_eq_zero_iff.mp
    calc
      (a * c) ^ 2 = (a * c * a) * c := by simp only [pow_two, mul_assoc]
      _ = 0 := by rw [haca, zero_mul]
  constructor
  · intro h
    have descend : ∀ n : ℕ, a ^ (n + 1) * b = 0 → a * b = 0 := by
      intro n
      induction n with
      | zero =>
          intro h
          simpa using h
      | succ n ih =>
          intro h
          apply ih
          have h' : a ^ 2 * (a ^ n * b) = 0 := by
            rw [pow_two]
            simpa only [pow_succ', mul_assoc] using h
          simpa only [pow_succ', mul_assoc] using square_step (a ^ n * b) h'
    cases m with
    | zero => exact (hm rfl).elim
    | succ n => exact descend n h
  · intro h
    exact pow_mul_eq_zero_of_le (m := 1) (Nat.pos_of_ne_zero hm)
      (by simpa only [pow_one] using h)

/-- A positive power has the same left annihilators as the element itself in a
reduced monoid with zero. This is the opposite-monoid form of `pow_mul_eq_zero_iff`. -/
@[simp]
theorem mul_pow_eq_zero_iff {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a b : M} {m : ℕ} (hm : m ≠ 0) : a * b ^ m = 0 ↔ a * b = 0 := by
  simpa only [← MulOpposite.op_pow, ← MulOpposite.op_mul, MulOpposite.op_eq_zero_iff] using
    (pow_mul_eq_zero_iff (a := MulOpposite.op b) (b := MulOpposite.op a) hm)

/-- Permuting a list in a reduced monoid with zero preserves whether its product is zero. -/
theorem List.Perm.prod_eq_zero_iff {M : Type u} [MonoidWithZero M] [IsReduced M]
    {l₁ l₂ : List M} (h : l₁.Perm l₂) : l₁.prod = 0 ↔ l₂.prod = 0 := by
  have insert_factor (x c y : M) (hxy : x * y = 0) : x * c * y = 0 := by
    have hyxc : y * (x * c) = 0 := by
      rw [← mul_assoc, IsReduced.mul_eq_zero_comm.mp hxy, zero_mul]
    exact IsReduced.mul_eq_zero_comm.mp hyxc
  -- Insert factors until the interchanged product has square zero.
  have interchange (x y z : M) (hxyz : x * y * z = 0) : x * z * y = 0 := by
    have hxzyz : x * z * (y * z) = 0 :=
      insert_factor x z (y * z) (by simpa only [mul_assoc] using hxyz)
    have hxzyxz : (x * z * y) * x * z = 0 :=
      insert_factor (x * z * y) x z (by simpa only [mul_assoc] using hxzyz)
    apply sq_eq_zero_iff.mp
    calc
      (x * z * y) ^ 2 = ((x * z * y) * x * z) * y := by
        simp only [pow_two, mul_assoc]
      _ = 0 := by rw [hxzyxz, zero_mul]
  have interchange_iff (x y z : M) : x * y * z = 0 ↔ x * z * y = 0 :=
    ⟨interchange x y z, interchange x z y⟩
  have swap_factors (p a b t : M) :
      p * (a * (b * t)) = 0 ↔ p * (b * (a * t)) = 0 := by
    calc
      p * (a * (b * t)) = 0 ↔ t * (p * a * b) = 0 := by
        simpa only [mul_assoc] using
          (IsReduced.mul_eq_zero_comm (a := p * a * b) (b := t))
      _ ↔ t * (p * b * a) = 0 := by
        simpa only [mul_assoc] using interchange_iff (t * p) a b
      _ ↔ p * (b * (a * t)) = 0 := by
        simpa only [mul_assoc] using
          (IsReduced.mul_eq_zero_comm (a := t) (b := p * b * a))
  -- Keep a prefix in the induction: a zero product need not have a zero tail.
  have prefixed : ∀ p : M, p * l₁.prod = 0 ↔ p * l₂.prod = 0 := by
    induction h with
    | nil =>
        intro p
        rfl
    | cons a h ih =>
        intro p
        simpa only [List.prod_cons, mul_assoc] using ih (p * a)
    | swap a b l =>
        intro p
        simp only [List.prod_cons]
        exact swap_factors _ _ _ _
    | trans h₁ h₂ ih₁ ih₂ =>
        intro p
        exact (ih₁ p).trans (ih₂ p)
  simpa only [one_mul] using prefixed 1


private theorem prod_eq_zero_of_cons_mem
    {M : Type u} [MonoidWithZero M] [IsReduced M]
    {a : M} {l : List M} (ha : a ∈ l) (hz : (a :: l).prod = 0) :
    l.prod = 0 := by
  have split : ∀ l : List M, a ∈ l → ∃ s t, l = s ++ a :: t := by
    intro l
    induction l with
    | nil =>
      intro hm
      simp only [List.not_mem_nil] at hm
    | cons b l ih =>
      intro hm
      rcases List.mem_cons.mp hm with hab | hm
      · subst b
        exact ⟨[], l, rfl⟩
      · obtain ⟨s, t, rfl⟩ := ih hm
        exact ⟨b :: s, t, rfl⟩
  obtain ⟨s, t, rfl⟩ := split l ha
  have hp : (s ++ a :: t).Perm (a :: (s ++ t)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (List.Perm.append_right t
        (List.perm_append_comm (l₁ := s) (l₂ := [a])))
  apply hp.prod_eq_zero_iff.mpr
  have hh := (List.perm_cons a).mpr hp
  have hs : a ^ 2 * (s ++ t).prod = 0 := by
    simpa only [List.prod_cons, pow_two, mul_assoc] using hh.prod_eq_zero_iff.mp hz
  simpa only [List.prod_cons] using
    (pow_mul_eq_zero_iff (m := 2) (by decide)).mp hs

/-- In a reduced monoid with zero, vanishing of an ordered product is preserved when its
membership support is enlarged, regardless of order or multiplicity. -/
theorem List.prod_eq_zero_of_subset
    {M : Type u} [MonoidWithZero M] [IsReduced M]
    {l₁ l₂ : List M} (h : List.Subset l₁ l₂) (hz : l₁.prod = 0) :
    l₂.prod = 0 := by
  suffices hdrop : ∀ (l : List M), l ⊆ l₂ → (l ++ l₂).prod = 0 → l₂.prod = 0 by
    apply hdrop l₁ h
    simp only [List.prod_append, hz, zero_mul]
  intro l
  induction l with
  | nil =>
    intro _ hz'
    simpa only [List.nil_append] using hz'
  | cons a l ih =>
    intro h' hz'
    apply ih
    · intro x hx
      exact h' (by simp only [List.mem_cons]; exact Or.inr hx)
    · apply prod_eq_zero_of_cons_mem (a := a)
      · simp only [List.mem_append]
        exact Or.inr (h' (by simp))
      · exact hz'

-- Reordering the support and deleting a repeated factor preserve vanishing.
example {M : Type u} [MonoidWithZero M] [IsReduced M] (a b c : M) :
    [a, b, a, c].prod = 0 ↔ [c, b, a].prod = 0 := by
  constructor
  · intro hz
    apply List.prod_eq_zero_of_subset (l₁ := [a, b, a, c]) ?_ hz
    intro x hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl | hx <;> simp_all
  · intro hz
    apply List.prod_eq_zero_of_subset (l₁ := [c, b, a]) ?_ hz
    intro x hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | rfl | hx <;> simp_all
