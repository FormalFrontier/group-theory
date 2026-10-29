/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.QuotientGroup
public import GroupTheory.Topology.Ultrafilter
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.ZMod

/-!
# An indiscrete quotient of index three

The dense kernel of a surjective additive homomorphism from the product `ℕ → ZMod 3`
gives an indiscrete, nondiscrete quotient of index three, with its quotient topology.
An abstract additive equivalence with `ZMod 3` does not identify this topology with the
discrete topology on `ZMod 3`.
-/

@[expose] public section

open Set

/-- A product of discrete groups has an additive quotient of index three whose inherited
topology is indiscrete and not discrete. -/
theorem exists_indiscrete_quotient_zmod_three :
    ∃ f : (ℕ → ZMod 3) →+ ZMod 3,
      Function.Surjective f ∧ Dense (f.ker : Set (ℕ → ZMod 3)) ∧ f.ker.index = 3 ∧
        (inferInstance : TopologicalSpace ((ℕ → ZMod 3) ⧸ f.ker)) = ⊤ ∧
          ¬ DiscreteTopology ((ℕ → ZMod 3) ⧸ f.ker) := by
  obtain ⟨f, hf, hd, hi, hp, hno, hnc⟩ :=
    AddMonoidHom.exists_surjective_dense_ker_pi_of_nontrivial (ι := ℕ) (H := ZMod 3)
  refine ⟨f, hf, hd, ?_, QuotientAddGroup.topology_eq_top_iff_dense.mpr hd, ?_⟩
  · simpa using hi
  · intro hdisc
    apply hno
    rw [← QuotientAddGroup.preimage_mk_zero f.ker]
    exact (QuotientAddGroup.isQuotientMap_mk f.ker).continuous.isOpen_preimage _
      (@isOpen_discrete _ _ hdisc _)
