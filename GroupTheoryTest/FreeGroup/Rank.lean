/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.FreeGroup.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite free bases and an index-two subgroup

The parity homomorphism from `FreeGroup (Fin 2)` to `Multiplicative (ZMod 2)` sends
the first generator to the nonidentity element and the second to the identity. Its
kernel has index two; its freeness and finite generation follow from Mathlib.
The rank calculation uses the free-basis comparison and finite-index rank formula.
It does not enumerate all index-two subgroups or give their generators.
-/

@[expose] public section

namespace GroupTheoryTest.FreeGroupRank

universe u

private def parity : FreeGroup (Fin 2) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun i ↦ if i = 0 then Multiplicative.ofAdd 1 else 1

private theorem parity_generator_zero :
    parity (FreeGroup.of (0 : Fin 2)) = Multiplicative.ofAdd 1 := by
  simp [parity]

private theorem parity_generator_one : parity (FreeGroup.of (1 : Fin 2)) = 1 := by
  simp [parity]

private theorem parity_generator_zero_ne_one : parity (FreeGroup.of (0 : Fin 2)) ≠ 1 := by
  rw [parity_generator_zero]
  decide

private theorem parity_surjective : Function.Surjective parity := by
  intro x
  have hx : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
    revert x
    decide
  rcases hx with rfl | rfl
  · exact ⟨1, map_one parity⟩
  · exact ⟨FreeGroup.of 0, parity_generator_zero⟩

private theorem parity_kernel_index : parity.ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr parity_surjective,
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide

private instance parityKernelFiniteIndex : parity.ker.FiniteIndex :=
  ⟨by rw [parity_kernel_index]; decide⟩

private theorem parity_ambient_isFreeGroup : IsFreeGroup (FreeGroup (Fin 2)) :=
  inferInstance

private theorem parity_ambient_fg : Group.FG (FreeGroup (Fin 2)) := inferInstance

private theorem parity_kernel_isFreeGroup : IsFreeGroup parity.ker := inferInstance

private theorem parity_kernel_fg : Group.FG parity.ker := inferInstance

private theorem parity_ambient_rank : Group.rank (FreeGroup (Fin 2)) = 2 := by
  simpa using (FreeGroupBasis.ofFreeGroup (Fin 2)).natCard_eq_rank.symm

private theorem parity_kernel_rank : Group.rank parity.ker = 3 := by
  have h := Subgroup.rank_add_index_eq parity.ker
  rw [parity_kernel_index, parity_ambient_rank] at h
  omega

private instance parityBasisIndexFinite : Finite (IsFreeGroup.Generators parity.ker) :=
  (IsFreeGroup.basis parity.ker).finite

private noncomputable def parityKernelBasis :
    FreeGroupBasis (Fin (Group.rank parity.ker)) parity.ker :=
  (IsFreeGroup.basis parity.ker).reindex
    (Finite.equivFinOfCardEq (IsFreeGroup.basis parity.ker).natCard_eq_rank)

private theorem parityKernelBasis_apply (i : Fin (Group.rank parity.ker)) :
    parityKernelBasis i = IsFreeGroup.basis parity.ker
      ((Finite.equivFinOfCardEq (IsFreeGroup.basis parity.ker).natCard_eq_rank).symm i) :=
  (IsFreeGroup.basis parity.ker).reindex_apply _ i

private theorem parityKernelBasis_repr :
    parityKernelBasis.repr = (IsFreeGroup.basis parity.ker).repr.trans
      (FreeGroup.freeGroupCongr
        (Finite.equivFinOfCardEq (IsFreeGroup.basis parity.ker).natCard_eq_rank)) :=
  rfl

private noncomputable def parityKernelBasisThree : FreeGroupBasis (Fin 3) parity.ker :=
  parityKernelBasis.reindex (finCongr parity_kernel_rank)

private theorem parityKernelBasisThree_repr_apply (i : Fin 3) :
    parityKernelBasisThree.repr (parityKernelBasisThree i) = FreeGroup.of i :=
  parityKernelBasisThree.repr_apply_coe i

private theorem empty_basis_rank : Group.rank (FreeGroup (Fin 0)) = 0 :=
  Group.rank_eq_zero _

private theorem top_boundary (G : Type u) [Group G] [Group.FG G] :
    Group.rank (⊤ : Subgroup G) + (⊤ : Subgroup G).index =
      Group.rank G * (⊤ : Subgroup G).index + 1 := by
  rw [Group.rank_congr Subgroup.topEquiv]
  simp

private theorem rank_one_boundary (H : Subgroup (FreeGroup (Fin 1))) [H.FiniteIndex] :
    Group.rank H = 1 := by
  have h := H.rank_add_index_eq
  have hG : Group.rank (FreeGroup (Fin 1)) = 1 := by
    simpa using (FreeGroupBasis.ofFreeGroup (Fin 1)).natCard_eq_rank.symm
  rw [hG, one_mul] at h
  omega

end GroupTheoryTest.FreeGroupRank
