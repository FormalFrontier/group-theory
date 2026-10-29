/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.ContinuousMap.Quotient
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact-open descent for the real projection

The projection from `ℝ × Bool` onto `ℝ` has the continuous section `r ↦ (r, false)`.
Its compact lifts are the images of compact sets under this section, namely `K × {false}`.
Neither the source nor the quotient is compact.
-/

@[expose] public section

open Topology

local instance : TopologicalSpace Bool := ⊥

namespace ContinuousMap

private def realBoolProjection : C(ℝ × Bool, ℝ) := ContinuousMap.fst

private def realBoolSection : C(ℝ, ℝ × Bool) :=
  (ContinuousMap.id ℝ).prodMk (ContinuousMap.const ℝ false)

private theorem realBoolSection_rightInverse :
    Function.RightInverse realBoolSection realBoolProjection := fun _ ↦ rfl

private noncomputable def realBoolPullbackHomeomorph :
    C(ℝ, ℝ) ≃ₜ {g : C(ℝ × Bool, ℝ) // Function.FactorsThrough g realBoolProjection} :=
  quotientPullbackHomeomorphOfRightInverse realBoolProjection realBoolSection
    realBoolSection_rightInverse

example (g : {g : C(ℝ × Bool, ℝ) // Function.FactorsThrough g realBoolProjection}) (r : ℝ) :
    realBoolPullbackHomeomorph.symm g r = g.val (r, false) :=
  quotientPullbackHomeomorphOfRightInverse_symm_apply realBoolProjection realBoolSection
    realBoolSection_rightInverse g r

end ContinuousMap
