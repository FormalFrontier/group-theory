/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor
import Mathlib.Topology.Instances.ZMod

/-!
# Right invariance and separation by finite quotient maps

The pointwise quotient equation implies right invariance under the returned
open normal subgroup, with no algebraic structure on the target. A nonconstant
Boolean-valued map on the cyclic group of order two forces the subgroup to
exclude the nonidentity element. The quotient's finiteness and discreteness
come from Mathlib's open-subgroup APIs.
-/

namespace GroupTheoryTest.Topology.Algebra.CompactGroup.DiscreteFactor

private theorem exists_right_invariant_openNormalSubgroup
    {G : Type*} {Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace Y] [DiscreteTopology Y]
    (f : C(G, Y)) :
    ∃ N : OpenNormalSubgroup G, ∀ g n : G, n ∈ N → f (g * n) = f g := by
  obtain ⟨N, fbar, hfactor⟩ := f.exists_openNormalSubgroup_factor
  refine ⟨N, fun g n hn => ?_⟩
  have hnq : (QuotientGroup.mk n : G ⧸ N.toSubgroup) = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  calc
    f (g * n) = fbar (QuotientGroup.mk (g * n)) := (hfactor _).symm
    _ = fbar (QuotientGroup.mk g) := by rw [QuotientGroup.mk_mul, hnq, mul_one]
    _ = f g := hfactor g

private def isNonzero : C(Multiplicative (ZMod 2), Bool) :=
  ⟨fun g => if g.toAdd = 0 then false else true, continuous_of_discreteTopology⟩

example : isNonzero 1 = false := by
  decide

example : isNonzero (Multiplicative.ofAdd (1 : ZMod 2)) = true := by
  decide

example : ∃ N : OpenNormalSubgroup (Multiplicative (ZMod 2)),
    Finite (Multiplicative (ZMod 2) ⧸ N.toSubgroup) ∧
    DiscreteTopology (Multiplicative (ZMod 2) ⧸ N.toSubgroup) ∧
    Multiplicative.ofAdd (1 : ZMod 2) ∉ N := by
  obtain ⟨N, fbar, hfactor⟩ := isNonzero.exists_openNormalSubgroup_factor
  refine ⟨N, Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen,
    QuotientGroup.discreteTopology N.isOpen, ?_⟩
  intro hmem
  have hquot :
      (QuotientGroup.mk (Multiplicative.ofAdd (1 : ZMod 2)) :
        Multiplicative (ZMod 2) ⧸ N.toSubgroup) = QuotientGroup.mk 1 := by
    simpa only [QuotientGroup.mk_one] using (QuotientGroup.eq_one_iff _).mpr hmem
  have hvalues : isNonzero (Multiplicative.ofAdd (1 : ZMod 2)) = isNonzero 1 :=
    (hfactor _).symm.trans ((congrArg fbar hquot).trans (hfactor _))
  exact (by decide : isNonzero (Multiplicative.ofAdd (1 : ZMod 2)) ≠ isNonzero 1) hvalues

example : ∃ N : OpenNormalSubgroup (Multiplicative (ZMod 2)),
    ∀ g n : Multiplicative (ZMod 2), n ∈ N → isNonzero (g * n) = isNonzero g :=
  exists_right_invariant_openNormalSubgroup isNonzero

end GroupTheoryTest.Topology.Algebra.CompactGroup.DiscreteFactor
