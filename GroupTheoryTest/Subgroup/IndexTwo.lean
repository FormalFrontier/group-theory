/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Subgroup.IndexTwo
import Mathlib.Algebra.Group.PUnit
import Mathlib.Tactic.NormNum

/-!
# Two-element and trivial-group character models

The two-element identity homomorphism and its bottom kernel give independent
nonvacuity witnesses. Both word-generation premises hold in this nonfree group.
The trivial group has neither an index-two subgroup nor a nontrivial character.
-/

private def twoNonidentity : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd 1

private theorem twoGroup_card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  simp [Nat.card_eq_fintype_card]

private theorem twoNonidentity_ne_one : twoNonidentity ≠ 1 := by
  change (1 : ZMod 2) ≠ 0
  exact one_ne_zero

private theorem twoGroup_index : (⊥ : Subgroup (Multiplicative (ZMod 2))).index = 2 := by
  rw [Subgroup.index_bot, twoGroup_card]

private theorem twoGroup_generator :
    Subgroup.closure ({twoNonidentity} : Set (Multiplicative (ZMod 2))) = ⊤ := by
  simpa only [Subgroup.zpowers_eq_closure] using
    (zpowers_eq_top_of_prime_card twoGroup_card twoNonidentity_ne_one)

private theorem twoGroup_inside_premises :
    Subgroup.closure ({twoNonidentity, 1} : Set (Multiplicative (ZMod 2))) = ⊤ ∧
      twoNonidentity ∉ (⊥ : Subgroup (Multiplicative (ZMod 2))) ∧
      (1 : Multiplicative (ZMod 2)) ∈ (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
  refine ⟨?_, ?_, Subgroup.one_mem _⟩
  · rw [Set.pair_comm, Subgroup.closure_insert_one]
    exact twoGroup_generator
  · simpa only [Subgroup.mem_bot] using twoNonidentity_ne_one

private theorem twoGroup_outside_premises :
    Subgroup.closure ({twoNonidentity, twoNonidentity} :
      Set (Multiplicative (ZMod 2))) = ⊤ ∧
      twoNonidentity ∉ (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
  constructor
  · simpa using twoGroup_generator
  · exact twoGroup_inside_premises.2.1

private theorem twoGroup_identity_nontrivial :
    MonoidHom.id (Multiplicative (ZMod 2)) ≠ 1 := by
  intro h
  have hg := DFunLike.congr_fun h twoNonidentity
  exact twoNonidentity_ne_one hg

private theorem twoGroup_kernel_classification
    (χ : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2)) :
    (χ.ker = ⊥ → χ = MonoidHom.id _) ∧ (χ.ker.index = 2 ↔ χ ≠ 1) := by
  constructor
  · intro hχ
    apply MonoidHom.ker_injective_of_card_eq_two twoGroup_card
    exact hχ.trans MonoidHom.ker_id.symm
  · exact MonoidHom.ker_index_eq_two_iff twoGroup_card χ

private theorem twoGroup_character_contract :
    let H : Subgroup (Multiplicative (ZMod 2)) := ⊥
    H.characterOfIndexTwo twoGroup_index 1 = 1 ∧
      H.characterOfIndexTwo twoGroup_index twoNonidentity = twoNonidentity ∧
      (H.characterOfIndexTwo twoGroup_index).ker = H ∧
      H.characterOfIndexTwo twoGroup_index ≠ 1 ∧
      (MonoidHom.id (Multiplicative (ZMod 2)) = H.characterOfIndexTwo twoGroup_index ↔
        (MonoidHom.id (Multiplicative (ZMod 2))).ker = H) ∧
      ∃! χ : Multiplicative (ZMod 2) →* Multiplicative (ZMod 2), χ ≠ 1 ∧ χ.ker = H := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.characterOfIndexTwo_apply_eq_one_iff _ twoGroup_index 1).mpr
      (Subgroup.one_mem _)
  · exact Subgroup.characterOfIndexTwo_apply_of_notMem _ twoGroup_index _
      twoGroup_inside_premises.2.1
  · exact Subgroup.ker_characterOfIndexTwo _ twoGroup_index
  · exact Subgroup.characterOfIndexTwo_ne_one _ twoGroup_index
  · exact Subgroup.eq_characterOfIndexTwo_iff _ twoGroup_index _
  · exact (Subgroup.index_eq_two_iff_existsUnique_nontrivial_hom _).mp twoGroup_index

private theorem twoGroup_correspondence :
    (Subgroup.indexTwoEquivNontrivialHom
      ⟨(⊥ : Subgroup (Multiplicative (ZMod 2))), twoGroup_index⟩).val = MonoidHom.id _ ∧
      ((Subgroup.indexTwoEquivNontrivialHom (G := Multiplicative (ZMod 2))).symm
        ⟨MonoidHom.id _, twoGroup_identity_nontrivial⟩).val = ⊥ ∧
      (MonoidHom.id (Multiplicative (ZMod 2))).ker.characterOfIndexTwo
        ((MonoidHom.ker_index_eq_two_iff twoGroup_card (MonoidHom.id _)).mpr
          twoGroup_identity_nontrivial) = MonoidHom.id _ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.indexTwoEquivNontrivialHom_apply_val]
    exact (Subgroup.characterOfIndexTwo_unique _ twoGroup_index _
      MonoidHom.ker_id).symm
  · rw [Subgroup.indexTwoEquivNontrivialHom_symm_apply_val, MonoidHom.ker_id]
  · exact Subgroup.characterOfIndexTwo_ker _ twoGroup_identity_nontrivial

private theorem twoGroup_projection_surjective :
    Function.Surjective (MonoidHom.fst (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 2))) := fun g => ⟨(g, 1), rfl⟩

private theorem twoGroup_pullback_character :
    let H : Subgroup (Multiplicative (ZMod 2)) := ⊥
    let f := MonoidHom.fst (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2))
    (H.comap f).index = 2 ∧
      (H.comap f).characterOfIndexTwo
        ((H.index_comap_of_surjective twoGroup_projection_surjective).trans twoGroup_index) =
        (H.characterOfIndexTwo twoGroup_index).comp f := by
  dsimp only
  constructor
  · exact ((⊥ : Subgroup (Multiplicative (ZMod 2))).index_comap_of_surjective
      twoGroup_projection_surjective).trans twoGroup_index
  · exact Subgroup.characterOfIndexTwo_comap _ twoGroup_index _
      twoGroup_projection_surjective

private theorem twoGroup_inside_word_generation :
    Subgroup.closure ({twoNonidentity ^ 2, 1, twoNonidentity * 1 * twoNonidentity⁻¹} :
      Set (Multiplicative (ZMod 2))) = ⊥ := by
  exact Subgroup.closure_sq_pair_conj_eq_of_index_eq_two _ twoGroup_index
    twoNonidentity 1 twoGroup_inside_premises.1 twoGroup_inside_premises.2.1
    twoGroup_inside_premises.2.2

private theorem twoGroup_outside_word_generation :
    Subgroup.closure ({twoNonidentity ^ 2, twoNonidentity * twoNonidentity⁻¹,
      twoNonidentity * twoNonidentity} : Set (Multiplicative (ZMod 2))) = ⊥ := by
  exact Subgroup.closure_sq_pair_mul_eq_of_index_eq_two _ twoGroup_index
    twoNonidentity twoNonidentity twoGroup_outside_premises.1
    twoGroup_outside_premises.2 twoGroup_outside_premises.2

private theorem trivial_group_boundary :
    IsEmpty {H : Subgroup PUnit // H.index = 2} ∧
      IsEmpty {χ : PUnit →* Multiplicative (ZMod 2) // χ ≠ 1} := by
  constructor
  · refine ⟨fun H => ?_⟩
    have htop : H.val = ⊤ := by
      apply top_unique
      intro g _
      have hg : g = 1 := Subsingleton.elim _ _
      rw [hg]
      exact H.val.one_mem
    have hindex := H.property
    rw [htop, Subgroup.index_top] at hindex
    norm_num at hindex
  · exact ⟨fun χ => χ.property (Subsingleton.elim _ _)⟩
