/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Finsupp.CoefficientSum
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Coefficient-sum relations with a noncancellative target

The source has natural-number scalars, integer coefficients and an infinite
index type. Its nonzero kernel element is a sum of two distinguished-singleton
relations. The same coefficient sum maps into `ℤ × WithTop ℕ`, with proper
nonzero image, and the unique factor is the inclusion into the first coordinate.
The displayed target witnesses failure of cancellation and additive inverses.
-/

open Finsupp

example :
    let σ : (ℕ →₀ ℤ) →ₗ[ℕ] ℤ := lsum ℕ (fun _ => LinearMap.id)
    let f : ℕ →₀ ℤ := single 1 3 - single 2 3
    let t : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ) := LinearMap.id.prod 0
    let T := t.comp σ
    f ≠ 0 ∧ f ∈ LinearMap.ker σ ∧
    f = (single 1 3 - single 0 3) + (single 2 (-3) - single 0 (-3)) ∧
    f ∈ Submodule.span ℕ
      (Set.range fun p : ℕ × ℤ => single p.1 p.2 - single 0 p.2) ∧
    (∃! u : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ), u.comp σ = T) ∧
    (∀ u : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ), u.comp σ = T → u = t) ∧
    (∀ z, t z = (z, 0)) ∧ T (single 0 1) = (1, 0) ∧
    ((1, 0) : ℤ × WithTop ℕ) ≠ 0 ∧ (¬ ∃ g, T g = (0, 1)) ∧
    ((0, ⊤) : ℤ × WithTop ℕ) + (0, 0) = (0, ⊤) + (0, 1) ∧
    ((0, 0) : ℤ × WithTop ℕ) ≠ (0, 1) ∧
    ¬ (∃ y : ℤ × WithTop ℕ, (0, ⊤) + y = 0) := by
  classical
  dsimp only
  let σ : (ℕ →₀ ℤ) →ₗ[ℕ] ℤ := lsum ℕ (fun _ => LinearMap.id)
  let f : ℕ →₀ ℤ := single 1 3 - single 2 3
  let t : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ) := LinearMap.id.prod 0
  let T := t.comp σ
  have hf : f ≠ 0 := by
    intro h
    have hv := congrArg (fun g : ℕ →₀ ℤ => g 1) h
    norm_num [f, single_apply] at hv
  have hk : f ∈ LinearMap.ker σ := by
    change σ (single 1 3 - single 2 3) = 0
    rw [map_sub]
    simp [σ]
  have hd : f = (single 1 3 - single 0 3) +
      (single 2 (-3) - single 0 (-3)) := by
    simp only [f, single_neg]
    abel
  have hs : f ∈ Submodule.span ℕ
      (Set.range fun p : ℕ × ℤ => single p.1 p.2 - single 0 p.2) := by
    rw [← ker_lsum_id 0]
    exact hk
  have hc : ∀ i m, T (single i m) = T (single 0 m) := by
    intro i m
    simp [T, σ]
  have hu : ∃! u : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ), u.comp σ = T :=
    (existsUnique_comp_lsum_id_iff 0 T).mpr hc
  have ht : ∀ u : ℤ →ₗ[ℕ] (ℤ × WithTop ℕ), u.comp σ = T → u = t := by
    intro u h
    rw [eq_comp_lsingle_of_comp_lsum_id_eq 0 T u h]
    apply LinearMap.ext
    intro z
    simp [T, σ]
  refine ⟨hf, hk, hd, hs, hu, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    rfl
  · simp
  · simp
  · rintro ⟨g, hg⟩
    have hv := congrArg Prod.snd hg
    simp at hv
  · simp
  · simp
  · rintro ⟨y, hy⟩
    have hv := congrArg Prod.snd hy
    simp at hv
