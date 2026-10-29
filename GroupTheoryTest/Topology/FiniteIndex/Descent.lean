/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.FiniteIndex.Descent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.NormNum

/-!
# A nonlinear continuous section

The projection from the discrete additive group `ℤ × ℤ` to `ℤ` admits the continuous
section `n ↦ (n, n²)`, which is not additive. Its kernel is nonzero and proper. The
finite-index subgroup `3ℤ` is proper, so the descent theorem has a nontrivial target.
-/

example :
    let r : ℤ × ℤ →+ ℤ := AddMonoidHom.fst ℤ ℤ
    let s : ℤ → ℤ × ℤ := fun n => (n, n ^ 2)
    (∀ N : AddSubgroup ℤ, N.FiniteIndex → IsOpen (N : Set ℤ)) ∧
      Continuous s ∧ (∀ n, r (s n) = n) ∧
      ¬ (∀ m n, s (m + n) = s m + s n) ∧
      r.ker ≠ ⊥ ∧ r.ker ≠ ⊤ ∧
      (AddSubgroup.zmultiples (3 : ℤ)).FiniteIndex ∧
      (AddSubgroup.zmultiples (3 : ℤ)) ≠ ⊥ ∧
      (AddSubgroup.zmultiples (3 : ℤ)) ≠ ⊤ := by
  let r : ℤ × ℤ →+ ℤ := AddMonoidHom.fst ℤ ℤ
  let s : ℤ → ℤ × ℤ := fun n => (n, n ^ 2)
  have hs : Continuous s := continuous_of_discreteTopology
  have hrs : ∀ n, r (s n) = n := fun _ => rfl
  have hG : ∀ N : AddSubgroup (ℤ × ℤ), N.FiniteIndex → IsOpen (N : Set (ℤ × ℤ)) :=
    fun N _ => isOpen_discrete _
  have hH := AddSubgroup.isOpen_finiteIndex_of_continuous_section r s hs hrs hG
  have hnonadd : ¬ (∀ m n, s (m + n) = s m + s n) := by
    intro h
    have hh := congrArg Prod.snd (h 1 1)
    norm_num [s] at hh
  have hker_bot : r.ker ≠ ⊥ := by
    intro h
    have hm : ((0, 1) : ℤ × ℤ) ∈ r.ker := rfl
    rw [h] at hm
    simp at hm
  have hker_top : r.ker ≠ ⊤ := by
    intro h
    have hm : ((1, 0) : ℤ × ℤ) ∈ r.ker := by rw [h]; trivial
    have he : (1 : ℤ) = 0 := hm
    norm_num at he
  have hindex : (AddSubgroup.zmultiples (3 : ℤ)).FiniteIndex := by
    apply AddSubgroup.finiteIndex_iff.mpr
    rw [Int.index_zmultiples]
    decide
  have hnonzero : AddSubgroup.zmultiples (3 : ℤ) ≠ ⊥ := by
    intro h
    have hm : (3 : ℤ) ∈ AddSubgroup.zmultiples (3 : ℤ) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨1, by simp⟩
    rw [h] at hm
    simp at hm
  have hproper : AddSubgroup.zmultiples (3 : ℤ) ≠ ⊤ := by
    intro h
    have hm : (1 : ℤ) ∈ AddSubgroup.zmultiples (3 : ℤ) := by rw [h]; trivial
    rw [AddSubgroup.mem_zmultiples_iff] at hm
    obtain ⟨n, hn⟩ := hm
    simp only [zsmul_eq_mul] at hn
    have hdiv : (3 : ℤ) ∣ 1 := ⟨n, by simpa [mul_comm] using hn.symm⟩
    norm_num at hdiv
  exact ⟨hH, hs, hrs, hnonadd, hker_bot, hker_top, hindex, hnonzero, hproper⟩
