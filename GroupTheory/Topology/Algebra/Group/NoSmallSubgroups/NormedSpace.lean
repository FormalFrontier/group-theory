/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# No small subgroups in real seminormed spaces

A real seminormed space, viewed as an additive group, has no small subgroups
exactly when its seminorm topology is Hausdorff. In particular, every real normed
space has no small subgroups; neither completeness nor finite dimension is needed.
The additive group is expressed using the canonical `Multiplicative` conversion.

The reverse implication uses a unit ball and the Archimedean growth of norms of
positive integer multiples. Hausdorffness is needed only to turn zero seminorm
into equality in a seminormed space. The forward implication reuses the general
Hausdorffness theorem for topological groups with no small subgroups.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u

section Seminormed

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real seminormed space has no small additive subgroups exactly when its
seminorm topology is Hausdorff. -/
theorem noSmallSubgroups_multiplicative_iff_t2Space :
    NoSmallSubgroups (Multiplicative E) ↔ T2Space E := by
  constructor
  · intro h
    let : NoSmallSubgroups (Multiplicative E) := h
    exact inferInstanceAs (T2Space (Multiplicative E))
  · intro h
    let : T2Space E := h
    let U : Set (Multiplicative E) := {g | ‖Multiplicative.toAdd g‖ < 1}
    have hU : U ∈ 𝓝 (1 : Multiplicative E) := by
      change {x : E | ‖x‖ < 1} ∈ 𝓝 (0 : E)
      simpa only [Metric.ball, dist_eq_norm, sub_zero] using
        Metric.ball_mem_nhds (0 : E) (show 0 < (1 : ℝ) from zero_lt_one)
    refine NoSmallSubgroups.of_nhds_one_pow hU ?_
    intro g hg
    have hbound (n : ℕ) (hn : 0 < n) :
        (n : ℝ) * ‖Multiplicative.toAdd g‖ < 1 := by
      have hmem := hg n hn
      change ‖n • Multiplicative.toAdd g‖ < 1 at hmem
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul] at hmem
      have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnnonneg] using hmem
    have hzero : ‖Multiplicative.toAdd g‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖Multiplicative.toAdd g‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖Multiplicative.toAdd g‖)
      have hnpos : 0 < n := Nat.cast_pos.mp ((one_div_pos.mpr hpos).trans hn)
      have hlarge : 1 < (n : ℝ) * ‖Multiplicative.toAdd g‖ :=
        (div_lt_iff₀ hpos).mp hn
      exact (not_lt_of_ge (le_of_lt hlarge)) (hbound n hnpos)
    have hclosure : Multiplicative.toAdd g ∈ closure ({0} : Set E) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      exact ⟨0, by simp, by simpa [dist_eq_norm, hzero] using hε⟩
    have hclosed : closure ({0} : Set E) = {0} := isClosed_singleton.closure_eq
    have hgzero : Multiplicative.toAdd g = 0 := by
      simpa only [hclosed, mem_singleton_iff] using hclosure
    simpa using congrArg Multiplicative.ofAdd hgzero

end Seminormed

/-- Every real normed space has no small additive subgroups, without completeness
or finite dimension. -/
instance NoSmallSubgroups.multiplicative_realNormedSpace
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NoSmallSubgroups (Multiplicative E) :=
  noSmallSubgroups_multiplicative_iff_t2Space.mpr inferInstance
