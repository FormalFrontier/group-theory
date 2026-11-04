/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Inseparability in spaces of continuous maps

For the compact-open topology, two continuous maps are inseparable exactly when
their values are inseparable at every point. No local compactness or separation
assumptions are needed.
-/

@[expose] public section

universe u v

namespace ContinuousMap

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- Continuous maps are inseparable in the compact-open topology exactly
when their values are inseparable at every point. -/
theorem inseparable_iff_forall_eval {F H : C(A, B)} :
    Inseparable F H ↔ ∀ a : A, Inseparable (F a) (H a) := by
  constructor
  · intro hFH a
    exact hFH.map (continuous_eval_const a)
  · intro hFH
    apply inseparable_iff_forall_isOpen.2
    intro S hS
    change TopologicalSpace.GenerateOpen _ S at hS
    induction hS with
    | basic V hV =>
        rcases hV with ⟨K, _hK, U, hU, rfl⟩
        change Set.MapsTo F K U ↔ Set.MapsTo H K U
        constructor
        · intro hF a ha
          exact ((inseparable_iff_forall_isOpen.1 (hFH a)) U hU).1 (hF ha)
        · intro hH a ha
          exact ((inseparable_iff_forall_isOpen.1 (hFH a)) U hU).2 (hH ha)
    | univ =>
        exact Iff.rfl
    | inter S T hS hT ihS ihT =>
        exact and_congr ihS ihT
    | sUnion S hS ihS =>
        change (∃ U ∈ S, F ∈ U) ↔ (∃ U ∈ S, H ∈ U)
        constructor
        · rintro ⟨U, hU, hFU⟩
          exact ⟨U, hU, (ihS U hU).1 hFU⟩
        · rintro ⟨U, hU, hHU⟩
          exact ⟨U, hU, (ihS U hU).2 hHU⟩

end ContinuousMap
