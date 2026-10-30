/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.FiniteIndex.Ascent
import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# A nonsplit cyclic extension

Reduction from the cyclic group of order four to that of order two has nontrivial
kernel and no homomorphic section. It is a finite discrete example of finite-index
openness ascending from a kernel and target without a splitting hypothesis.
-/

open Multiplicative

/-- Reduction modulo two is a nonsplit example of kernel/target ascent. -/
example :
    let q : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
      (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative
    q.ker ≠ ⊥ ∧
      (¬ ∃ s : Multiplicative (ZMod 2) →* Multiplicative (ZMod 4),
        q.comp s = MonoidHom.id _) ∧
      ∀ K : Subgroup (Multiplicative (ZMod 4)),
        K.FiniteIndex → IsOpen (K : Set (Multiplicative (ZMod 4))) := by
  dsimp only
  let q : Multiplicative (ZMod 4) →* Multiplicative (ZMod 2) :=
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative
  change q.ker ≠ ⊥ ∧ _
  constructor
  · intro hker
    have hx : ofAdd (2 : ZMod 4) ∈ q.ker := by decide
    have hx1 : ofAdd (2 : ZMod 4) = 1 := Subgroup.mem_bot.mp (hker ▸ hx)
    exact (by decide : ofAdd (2 : ZMod 4) ≠ 1) hx1
  constructor
  · rintro ⟨s, hs⟩
    have hs2 : s (ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
      rw [← map_pow]
      have h2 : ofAdd (1 : ZMod 2) ^ 2 = 1 := by decide
      rw [h2, map_one]
    have himage : q (s (ofAdd (1 : ZMod 2))) = ofAdd (1 : ZMod 2) :=
      DFunLike.congr_fun hs _
    have hnonsplit : ∀ x : Multiplicative (ZMod 4),
        x ^ 2 = 1 → q x ≠ ofAdd (1 : ZMod 2) := by decide
    exact hnonsplit _ hs2 himage
  · apply Subgroup.isOpen_finiteIndex_of_ker q continuous_of_discreteTopology
    · exact ZMod.castHom_surjective (by decide : 2 ∣ 4)
    · intro H _
      exact isOpen_discrete _
    · intro H _
      exact isOpen_discrete _
