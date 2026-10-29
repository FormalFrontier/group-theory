/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.LocallyClosed

/-!
# Closure of intersections of locally closed additive subgroups

This client uses the additive API on the supplied addition, negation and topology,
without assuming jointly continuous addition. Closedness of the two locally
closed subgroups makes closure commute with their intersection.
-/

open Topology

universe u

private theorem closure_inf_of_isLocallyClosed
    {A : Type u} [AddGroup A] [TopologicalSpace A]
    [SeparatelyContinuousAdd A] [ContinuousNeg A]
    (H K : AddSubgroup A) (hH : IsLocallyClosed (H : Set A))
    (hK : IsLocallyClosed (K : Set A)) :
    closure ((H ⊓ K : AddSubgroup A) : Set A) =
      closure (H : Set A) ∩ closure (K : Set A) := by
  have hHclosed := H.isClosed_iff_isLocallyClosed.mpr hH
  have hKclosed := K.isClosed_iff_isLocallyClosed.mpr hK
  rw [AddSubgroup.coe_inf, (hHclosed.inter hKclosed).closure_eq,
    hHclosed.closure_eq, hKclosed.closure_eq]
