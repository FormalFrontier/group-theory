/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Characters of cyclic groups

Every nontrivial cyclic group has a nontrivial circle-valued character.
The finite case transports `ZMod.toCircle` along `zmodCyclicMulEquiv`;
the infinite case uses `intCyclicMulEquiv` and sends the integer generator to `-1`.
-/

@[expose] public section

universe u

namespace IsCyclic

variable (G : Type u) [Group G]

private theorem exists_circleHom_ne_one_of_finite [Finite G] [IsCyclic G] [Nontrivial G] :
    ∃ χ : G →* Circle, χ ≠ 1 := by
  let : NeZero (Nat.card G) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  let e := zmodCyclicMulEquiv (G := G) inferInstance
  let χ := (ZMod.toCircle (N := Nat.card G)).toMonoidHom.comp e.symm.toMonoidHom
  have hχ : Function.Injective χ := fun _ _ h =>
    e.symm.injective (ZMod.injective_toCircle h)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨χ, fun h => hg (hχ ?_)⟩
  simp only [h, MonoidHom.one_apply]

private theorem exists_circleHom_ne_one_of_infinite [Infinite G] [IsCyclic G] :
    ∃ χ : G →* Circle, χ ≠ 1 := by
  let e := intCyclicMulEquiv (G := G)
  let χ := (zpowersHom Circle (-1)).comp e.symm.toMonoidHom
  refine ⟨χ, fun h => Circle.neg_ne_self 1 ?_⟩
  have he := DFunLike.congr_fun h (e (Multiplicative.ofAdd 1))
  simpa [χ] using he

/-- A nontrivial cyclic group admits a nontrivial circle-valued character. -/
theorem exists_circleHom_ne_one [IsCyclic G] [Nontrivial G] :
    ∃ χ : G →* Circle, χ ≠ 1 := by
  obtain h | h := finite_or_infinite G
  · let : Finite G := h
    exact exists_circleHom_ne_one_of_finite G
  · let : Infinite G := h
    exact exists_circleHom_ne_one_of_infinite G

/-- A character of a nontrivial cyclic group can detect any specified generator. -/
theorem exists_circleHom_apply_ne_one [Nontrivial G] {g : G}
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ∃ χ : G →* Circle, χ g ≠ 1 := by
  let : IsCyclic G :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, top_unique fun x _ => hg x⟩
  obtain ⟨χ, hχ⟩ := exists_circleHom_ne_one G
  refine ⟨χ, fun h => hχ ?_⟩
  exact (MonoidHom.eq_iff_eq_on_generator hg χ 1).mpr (by simpa using h)

end IsCyclic
