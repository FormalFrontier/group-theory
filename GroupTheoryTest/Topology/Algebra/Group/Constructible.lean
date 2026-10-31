/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.LocallyClosed
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Constructible subgroups with continuous left translations

The canonical self-action supplies the given left-translation continuity;
inversion supplies the other half of separate continuity through the existing
bridge. Global constructibility then implies closedness through the public API.
-/

open Topology

example {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousConstSMul G G] [ContinuousInv G]
    (H : Subgroup G) (hH : IsConstructible (H : Set G)) : IsClosed (H : Set G) := by
  let : SeparatelyContinuousMul G :=
    separatelyContinuousMul_of_continuous_const_mul fun a ↦ by
      simpa only [smul_eq_mul] using (continuous_const_smul a : Continuous fun x : G ↦ a • x)
  exact H.isClosed_of_isLocallyConstructible hH.isLocallyConstructible
