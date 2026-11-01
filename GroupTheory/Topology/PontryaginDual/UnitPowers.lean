module

public import Mathlib.Analysis.Complex.Norm

import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Negative real parts of powers of unit complex numbers

A complex number of norm one other than one has a positive natural power with strictly
negative real part.

If every positive power had nonnegative real part, repeated squaring would make the positive
deficit from real part one grow at least geometrically while remaining at most one.
-/

@[expose] public section

namespace Complex

/-- A complex number of norm one other than `1` has a positive power with negative real part. -/
theorem exists_pow_re_neg {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ (z ^ n).re < 0 := by
  classical
  have hcoord (a : ℂ) (ha : ‖a‖ = 1) :
      a.re * a.re + a.im * a.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, ha]
    norm_num
  have hstart : 0 < 1 - z.re := by
    have hre := Complex.re_le_norm z
    rw [hz] at hre
    by_contra hnot
    have hrez : z.re = 1 := by
      have hle : 1 - z.re ≤ 0 := not_lt.mp hnot
      linarith
    have himsq : z.im * z.im = 0 := by
      have hc := hcoord z hz
      rw [hrez] at hc
      linarith
    have himz : z.im = 0 := (mul_eq_zero.mp himsq).elim id id
    exact hne (Complex.ext hrez himz)
  by_contra h
  have hnonneg (n : ℕ) (hn : 0 < n) : 0 ≤ (z ^ n).re := by
    by_contra hneg
    exact h ⟨n, hn, lt_of_not_ge hneg⟩
  let w : ℕ → ℂ := fun n => z ^ (2 ^ n)
  let d : ℕ → ℝ := fun n => 1 - (w n).re
  have hw_norm (n : ℕ) : ‖w n‖ = 1 := by
    change ‖z ^ (2 ^ n)‖ = 1
    rw [Complex.norm_pow, hz, one_pow]
  have hw_nonneg (n : ℕ) : 0 ≤ (w n).re := by
    exact hnonneg (2 ^ n) (pow_pos (by norm_num) n)
  have hw_succ (n : ℕ) : w (n + 1) = w n * w n := by
    change z ^ (2 ^ (n + 1)) = z ^ (2 ^ n) * z ^ (2 ^ n)
    rw [pow_succ, pow_mul, pow_two]
  have hd_zero : 0 < d 0 := by
    simpa only [d, w, pow_zero, pow_one] using hstart
  have hd_nonneg (n : ℕ) : 0 ≤ d n := by
    change 0 ≤ 1 - (w n).re
    have hre := Complex.re_le_norm (w n)
    rw [hw_norm n] at hre
    linarith
  have hd_le (n : ℕ) : d n ≤ 1 := by
    change 1 - (w n).re ≤ 1
    linarith [hw_nonneg n]
  have hrec (n : ℕ) :
      d (n + 1) = 2 * (1 + (w n).re) * d n := by
    have hc := hcoord (w n) (hw_norm n)
    change 1 - (w (n + 1)).re =
      2 * (1 + (w n).re) * (1 - (w n).re)
    rw [hw_succ n, Complex.mul_re]
    nlinarith
  have hstep (n : ℕ) : 2 * d n ≤ d (n + 1) := by
    have hprod : 0 ≤ (w n).re * d n :=
      mul_nonneg (hw_nonneg n) (hd_nonneg n)
    nlinarith [hrec n]
  have hgrow (n : ℕ) : ((n : ℝ) + 1) * d 0 ≤ d n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hprod : 0 ≤ (n : ℝ) * d 0 :=
        mul_nonneg (Nat.cast_nonneg n) (le_of_lt hd_zero)
      rw [Nat.cast_succ]
      nlinarith [hstep n]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / d 0)
  have hlt : 1 < (n : ℝ) * d 0 := (div_lt_iff₀ hd_zero).mp hn
  nlinarith [hgrow n, hd_le n]

end Complex
