/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Algebra.Algebra.Operations
public import GroupTheory.Ring.Nilpotent.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Nilpotency-class bounds for finite submodule sums and spans

For a finite supported pairwise commuting family of submodules of an algebra, the
sum's total nilpotency class is at most one plus the sum of the predecessors of the
summands' total nilpotency classes. No nilpotence hypothesis on the summands is
required. A nonnilpotent sum has total class zero; if the sum is nilpotent, containment
and monotonicity of powers force every supported summand to be nilpotent.

The finite-span bound assumes only pairwise commutation of the principal submodules
of the displayed generators. It follows by expressing the span as a finite sum of
principal submodules and preserving total nilpotency class through
`Submodule.spanSingleton`.

Both bounds include empty support, repeated values, and trivial carriers. The upper
bound is `1 + ∑ (nilpotencyClass _ - 1)`, with natural-number subtraction. No fixed
value for the total nilpotency class of zero in a trivial carrier is assumed.

## References

The submodule lattice and principal-span APIs are from Mathlib. The total nilpotency
class and its power-zero API are from `Mathlib.RingTheory.Nilpotent.Defs`, formalized
by Oliver Nash. The proof uses `Finset.sum_pow_eq_zero_of_pairwise_commute` from
`GroupTheory.Ring.Nilpotent.Finset`, followed by the power and map formulas for total
nilpotency class from `GroupTheory.Algebra.GroupWithZero.Nilpotent`.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace Submodule

/-- The total nilpotency class of a finite sum of supported pairwise commuting
submodules is at most one plus the sum of the predecessors of their total nilpotency
classes. No summand-nilpotence hypothesis is required; empty support, repeated values,
and trivial carriers are included. -/
public theorem nilpotencyClass_sum_le
    {R : Type u} {A : Type v} {ι : Type w}
    [CommSemiring R] [Semiring A] [Algebra R A]
    (s : Finset ι) (f : ι → Submodule R A)
    (hcomm : (s : Set ι).Pairwise (fun i j => Commute (f i) (f j))) :
    nilpotencyClass (∑ i ∈ s, f i) ≤
      1 + ∑ i ∈ s, (nilpotencyClass (f i) - 1) := by
  classical
  by_cases hsum : IsNilpotent (∑ i ∈ s, f i)
  · rcases subsingleton_or_nontrivial (Submodule R A) with hsub | hnontriv
    · let : Subsingleton (Submodule R A) := hsub
      rw [nilpotencyClass_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · let : Nontrivial (Submodule R A) := hnontriv
      have hnil : ∀ i ∈ s, IsNilpotent (f i) := by
        intro i hi
        have hle : f i ≤ ∑ j ∈ s, f j := by
          rw [Submodule.sum_eq_sup]
          exact Finset.le_sup hi
        refine IsNilpotent.mk (f i) (nilpotencyClass (∑ j ∈ s, f j)) ?_
        apply le_antisymm
        · calc
            (f i) ^ nilpotencyClass (∑ j ∈ s, f j) ≤
                (∑ j ∈ s, f j) ^ nilpotencyClass (∑ j ∈ s, f j) :=
              _root_.pow_le_pow_left' hle _
            _ = 0 := pow_nilpotencyClass hsum
        · rw [Submodule.zero_eq_bot]
          exact bot_le
      have hpow := Finset.sum_pow_eq_zero_of_pairwise_commute s f
        (fun i => nilpotencyClass (f i))
        (fun i hi => pow_nilpotencyClass (hnil i hi)) hcomm
      have hclass := nilpotencyClass_pow (∑ i ∈ s, f i)
        (1 + ∑ i ∈ s, (nilpotencyClass (f i) - 1))
      rw [hpow, nilpotencyClass_zero] at hclass
      have hN : 0 < 1 + ∑ i ∈ s, (nilpotencyClass (f i) - 1) := by omega
      have hlt :
          (nilpotencyClass (∑ i ∈ s, f i) +
              (1 + ∑ i ∈ s, (nilpotencyClass (f i) - 1)) - 1) /
            (1 + ∑ i ∈ s, (nilpotencyClass (f i) - 1)) < 2 := by
        omega
      have hmul := (Nat.div_lt_iff_lt_mul hN).mp hlt
      omega
  · have hzero : nilpotencyClass (∑ i ∈ s, f i) = 0 := by
      by_contra hne
      exact hsum (isNilpotent_of_pos_nilpotencyClass (Nat.pos_of_ne_zero hne))
    rw [hzero]
    exact Nat.zero_le _

/-- The total nilpotency class of a finite span is at most one plus the sum of the
predecessors of the generators' total nilpotency classes, provided their principal
submodules pairwise commute on the finite support. No commutation or nilpotence
hypothesis on the generators themselves is required. -/
public theorem nilpotencyClass_span_finset_le
    {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [Algebra R A]
    (s : Finset A)
    (hcomm : (s : Set A).Pairwise
      (fun x y => Commute (Submodule.spanSingleton R x) (Submodule.spanSingleton R y))) :
    nilpotencyClass (Submodule.span R (↑s : Set A)) ≤
      1 + ∑ x ∈ s, (nilpotencyClass x - 1) := by
  classical
  have hspan :
      (∑ x ∈ s, Submodule.spanSingleton R x) = Submodule.span R (↑s : Set A) := by
    calc
      (∑ x ∈ s, Submodule.spanSingleton R x) =
          s.sup (fun x => Submodule.spanSingleton R x) :=
        Submodule.sum_eq_sup s _
      _ = ⨆ x ∈ s, Submodule.spanSingleton R x := Finset.sup_eq_iSup s _
      _ = Submodule.span R (↑s : Set A) := by
        simpa only [Submodule.spanSingleton_apply, Finset.mem_coe] using
          (Submodule.span_eq_iSup_of_singleton_spans (R := R) (↑s : Set A)).symm
  have hreflect : ∀ x : A, Submodule.spanSingleton R x = 0 → x = 0 := by
    intro x hx
    rw [Submodule.spanSingleton_apply, Submodule.zero_eq_bot] at hx
    exact Submodule.span_singleton_eq_bot.mp hx
  have hbound := Submodule.nilpotencyClass_sum_le s (Submodule.spanSingleton R) hcomm
  rw [hspan] at hbound
  simpa only [nilpotencyClass_map (Submodule.spanSingleton R) hreflect] using hbound

end Submodule
