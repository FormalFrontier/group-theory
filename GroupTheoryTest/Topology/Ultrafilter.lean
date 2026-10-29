/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Ultrafilter
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# An order-three target for ultrafilter-limit homomorphisms

The given additive group `ZMod 3`, with its Mathlib discrete topology, is the target of a
surjective finite-image abstract homomorphism from its countable power. Its zero fiber is
dense and proper, and the homomorphism is not continuous. No topology instance is added.
-/

open Filter Set Topology

/-- A finite-image counterexample using the original addition on `ZMod 3`. -/
private theorem exists_zmod_three_hom :
    ∃ L : (ℕ → ZMod 3) →+ ZMod 3,
      Function.Surjective L ∧ (Set.range L).Finite ∧
      Dense {f | L f = 0} ∧ L (fun _ => 1) ≠ 0 ∧ ¬ Continuous L := by
  have : Fact (1 < 3) := ⟨by decide⟩
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (cofinite : Filter ℕ)
  refine ⟨U.limAddMonoidHom, U.limAddMonoidHom_surjective, Set.toFinite _,
    U.dense_fiber_limAddMonoidHom hU 0, ?_, U.not_continuous_limAddMonoidHom hU⟩
  simp
