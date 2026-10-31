/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.Cofinite
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.WithTopology

/-!
# Cofinite topologies coinduced by projections

The projections `ℤ × ZMod 2 → ℤ` and `ℤ × ℤ → ℤ` have finite and infinite kernels,
respectively. With the cofinite topology on each whole source carrier, their coinduced topologies
on `ℤ` are cofinite and indiscrete, respectively. These target topologies are distinct because
`ℤ` is infinite. The kernel and fiber proofs use Mathlib's subtype and finite-set injection API.

For a cofinite group, the canonical action on any coset quotient is separately continuous.
With the cofinite topology on `ℤ`, its quotient by `2ℤ` has a jointly continuous, nontrivial action
and distinct inseparable points in its quotient topology.
-/

@[expose] public section

example :
    Finite (AddMonoidHom.fst ℤ (ZMod 2)).ker ∧
    Infinite (AddMonoidHom.fst ℤ ℤ).ker ∧
    TopologicalSpace.coinduced
      (AddMonoidHom.fst ℤ (ZMod 2) : ℤ × ZMod 2 → ℤ)
      TopologicalSpace.cofinite = TopologicalSpace.cofinite ∧
    TopologicalSpace.coinduced
      (AddMonoidHom.fst ℤ ℤ : ℤ × ℤ → ℤ)
      TopologicalSpace.cofinite = ⊤ := by
  have hfinite : Finite (AddMonoidHom.fst ℤ (ZMod 2)).ker := by
    refine Finite.of_injective
      (fun x : (AddMonoidHom.fst ℤ (ZMod 2)).ker => x.val.2) ?_
    intro x y hxy
    apply Subtype.ext
    refine Prod.ext ?_ hxy
    have hx : x.val.1 = 0 := x.property
    have hy : y.val.1 = 0 := y.property
    exact hx.trans hy.symm
  have hinfinite : Infinite (AddMonoidHom.fst ℤ ℤ).ker := by
    refine Infinite.of_injective
      (fun z : ℤ => (⟨(0, z), rfl⟩ : (AddMonoidHom.fst ℤ ℤ).ker)) ?_
    intro z w hzw
    exact congrArg (fun x : (AddMonoidHom.fst ℤ ℤ).ker => x.val.2) hzw
  refine ⟨hfinite, hinfinite, ?_, ?_⟩
  · exact @AddMonoidHom.coinduced_eq_cofinite_of_finite_ker
      (ℤ × ZMod 2) ℤ _ _ TopologicalSpace.cofinite
      (AddMonoidHom.fst ℤ (ZMod 2)) rfl
      (fun a => ⟨(a, 0), rfl⟩) hfinite
  · refine CofiniteTopology.coinduced_eq_top_of_infinite_fibers
      (AddMonoidHom.fst ℤ ℤ : ℤ × ℤ → ℤ) ?_
    intro a
    refine Set.infinite_of_injective_forall_mem (f := fun z : ℤ => (a, z)) ?_ ?_
    · intro z w hzw
      exact congrArg Prod.snd hzw
    · intro z
      rfl

universe u

example {G : Type u} [Group G] [tG : TopologicalSpace G] (H : Subgroup G)
    (hG : tG = TopologicalSpace.cofinite) :
    (∀ g : G, Continuous (fun q : G ⧸ H => g • q)) ∧
      (∀ q : G ⧸ H, Continuous (fun g : G => g • q)) := by
  let : SeparatelyContinuousMul G :=
    { continuous_const_mul := fun {a} => CofiniteTopology.continuous_mul_left hG a
      continuous_mul_const := fun {a} => CofiniteTopology.continuous_mul_right hG a }
  constructor
  · intro g
    exact continuous_const_smul g
  · intro q
    refine QuotientGroup.induction_on q ?_
    intro a
    simpa only [Function.comp_def, MulAction.Quotient.smul_mk, smul_eq_mul] using
      (QuotientGroup.continuous_mk (N := H)).comp
        (CofiniteTopology.continuous_mul_right hG a)

example [tZ : TopologicalSpace ℤ] (hZ : tZ = TopologicalSpace.cofinite) :
    Continuous (fun p : ℤ × (ℤ ⧸ AddSubgroup.zmultiples (2 : ℤ)) => p.1 +ᵥ p.2) ∧
      (((1 : ℤ) +ᵥ (QuotientAddGroup.mk (0 : ℤ) :
          ℤ ⧸ AddSubgroup.zmultiples (2 : ℤ))) ≠ QuotientAddGroup.mk (0 : ℤ)) ∧
      Inseparable
        ((1 : ℤ) +ᵥ (QuotientAddGroup.mk (0 : ℤ) :
          ℤ ⧸ AddSubgroup.zmultiples (2 : ℤ)))
        (QuotientAddGroup.mk (0 : ℤ)) := by
  let : Infinite (AddSubgroup.zmultiples (2 : ℤ)) := by
    refine Infinite.of_injective
      (fun n : ℤ => (⟨2 * n, Int.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩ :
        AddSubgroup.zmultiples (2 : ℤ))) ?_
    intro m n h
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) (congrArg Subtype.val h)
  have hcontinuous :
      Continuous (fun p : ℤ × (ℤ ⧸ AddSubgroup.zmultiples (2 : ℤ)) => p.1 +ᵥ p.2) :=
    (QuotientAddGroup.continuous_vadd_iff (AddSubgroup.zmultiples (2 : ℤ)) hZ).mpr
      (Or.inr inferInstance)
  refine ⟨hcontinuous, ?_, ?_⟩
  · intro heq
    have hmem : (1 : ℤ) ∈ AddSubgroup.zmultiples (2 : ℤ) := by
      simpa only [AddAction.Quotient.vadd_mk, vadd_eq_add, add_zero,
        QuotientAddGroup.eq, neg_zero, zero_add] using heq.symm
    exact (by decide : ¬ (2 : ℤ) ∣ 1) (Int.mem_zmultiples_iff.mp hmem)
  · have hfrom : Continuous
        (WithTopology.ofTopology (X := ℤ) (t := TopologicalSpace.cofinite)) := by
      rw [hZ]
      exact WithTopology.continuous_ofTopology _
    let : PreirreducibleSpace ℤ :=
      (WithTopology.ofTopology_surjective TopologicalSpace.cofinite).preirreducibleSpace hfrom
    let : ContinuousNeg ℤ := ⟨CofiniteTopology.continuous_neg hZ⟩
    exact (AddAction.continuous_vadd_iff_inseparable.mp hcontinuous)
      (1 : ℤ) (QuotientAddGroup.mk (0 : ℤ))
