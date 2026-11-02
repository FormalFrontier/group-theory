module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# No small subgroups of the circle

The circle group has no small subgroups: its centered arc of radius `Real.pi / 2`
contains no nontrivial subgroup. The neighborhood basis and positive-powers
criterion are supplied by Mathlib's circle API.
-/

@[expose] public section

namespace Circle

/-- The circle group has no small subgroups, witnessed by its centered arc of
radius `Real.pi / 2`. -/
instance noSmallSubgroups : NoSmallSubgroups Circle := by
  refine NoSmallSubgroups.of_nhds_one_pow
    (U := centeredArc (Real.pi / 2)) ?_ ?_
  · apply hasBasis_centeredArc_div_two_pow.mem_iff.mpr
    exact ⟨0, trivial, by simp⟩
  · intro z hz
    exact eq_one_of_forall_pow_mem_centeredArc_pi_div_two hz

end Circle
