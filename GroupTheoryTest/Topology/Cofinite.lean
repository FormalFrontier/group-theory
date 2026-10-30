/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.Cofinite
import Mathlib.Data.ZMod.Basic

/-!
# Cofinite topologies coinduced by projections

The projections `ℤ × ZMod 2 → ℤ` and `ℤ × ℤ → ℤ` have finite and infinite kernels,
respectively. With the cofinite topology on each whole source carrier, their coinduced topologies
on `ℤ` are cofinite and indiscrete, respectively. These target topologies are distinct because
`ℤ` is infinite. The kernel and fiber proofs use Mathlib's subtype and finite-set injection API.
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
