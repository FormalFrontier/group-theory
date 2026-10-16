/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.FreeGroup.IndexTwo

/-!
# Canonical two-generator examples

The canonical free group basis realizes all three generator-value patterns.
Direct evaluations distinguish the three kernels and show that each is proper.
-/

@[expose] public section

namespace FreeGroupBasis.IndexTwoExamples

private abbrev F := FreeGroup (Fin 2)

private def canonicalBasis : FreeGroupBasis (Fin 2) F :=
  FreeGroupBasis.ofFreeGroup (Fin 2)

private abbrev a : F := FreeGroup.of 0

private abbrev b : F := FreeGroup.of 1

private theorem canonical_basis_values : canonicalBasis 0 = a ∧ canonicalBasis 1 = b := by
  constructor <;> rfl

private theorem canonical_character_apply (c : Fin 3) (i : Fin 2) :
    canonicalBasis.indexTwoCharacter c (FreeGroup.of i) =
      ![![Multiplicative.ofAdd (1 : ZMod 2), 1], ![1, Multiplicative.ofAdd 1],
        ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]] c i := by
  change FreeGroup.lift
      (![![Multiplicative.ofAdd (1 : ZMod 2), 1], ![1, Multiplicative.ofAdd 1],
        ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]] c) (FreeGroup.of i) = _
  exact FreeGroup.lift_apply_of

private theorem canonical_character_values :
    canonicalBasis.indexTwoCharacter 0 a = Multiplicative.ofAdd (1 : ZMod 2) ∧
    canonicalBasis.indexTwoCharacter 0 b = 1 ∧
    canonicalBasis.indexTwoCharacter 1 a = 1 ∧
    canonicalBasis.indexTwoCharacter 1 b = Multiplicative.ofAdd (1 : ZMod 2) ∧
    canonicalBasis.indexTwoCharacter 2 a = Multiplicative.ofAdd (1 : ZMod 2) ∧
    canonicalBasis.indexTwoCharacter 2 b = Multiplicative.ofAdd (1 : ZMod 2) := by
  simp only [a, b, canonical_character_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  decide

private theorem canonical_kernel_memberships :
    a ∉ (canonicalBasis.indexTwoCharacter 0).ker ∧
    b ∈ (canonicalBasis.indexTwoCharacter 0).ker ∧
    a ∈ (canonicalBasis.indexTwoCharacter 1).ker ∧
    b ∉ (canonicalBasis.indexTwoCharacter 1).ker ∧
    a ∉ (canonicalBasis.indexTwoCharacter 2).ker ∧
    b ∉ (canonicalBasis.indexTwoCharacter 2).ker := by
  simp only [MonoidHom.mem_ker, a, b, canonical_character_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  decide

private theorem canonical_kernels_distinct :
    (canonicalBasis.indexTwoCharacter 0).ker ≠ (canonicalBasis.indexTwoCharacter 1).ker ∧
    (canonicalBasis.indexTwoCharacter 0).ker ≠ (canonicalBasis.indexTwoCharacter 2).ker ∧
    (canonicalBasis.indexTwoCharacter 1).ker ≠ (canonicalBasis.indexTwoCharacter 2).ker := by
  rcases canonical_kernel_memberships with ⟨ha0, hb0, ha1, _, ha2, hb2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ha0 (h.symm ▸ ha1)
  · intro h
    exact hb2 (h ▸ hb0)
  · intro h
    exact ha2 (h ▸ ha1)

private theorem canonical_kernels_proper :
    (canonicalBasis.indexTwoCharacter 0).ker ≠ ⊤ ∧
    (canonicalBasis.indexTwoCharacter 1).ker ≠ ⊤ ∧
    (canonicalBasis.indexTwoCharacter 2).ker ≠ ⊤ := by
  rcases canonical_kernel_memberships with ⟨ha0, _, _, hb1, ha2, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ha0 (by rw [h]; trivial)
  · intro h
    exact hb1 (by rw [h]; trivial)
  · intro h
    exact ha2 (by rw [h]; trivial)

private theorem canonical_composite_mem :
    (a * b * a⁻¹) * b⁻¹ ∈ (canonicalBasis.indexTwoCharacter 0).ker := by
  simp [MonoidHom.mem_ker, a, b, map_mul, map_inv, canonical_character_apply]

private theorem canonical_index_two_classification (H : Subgroup F) :
    H.index = 2 ↔ ∃! c : Fin 3, H = (canonicalBasis.indexTwoCharacter c).ker :=
  canonicalBasis.index_eq_two_iff_existsUnique_indexTwoCharacter_ker H

private theorem canonical_kernel_generators (c : Fin 3) :
    Subgroup.closure (Set.range (canonicalBasis.indexTwoGenerators c)) =
      (canonicalBasis.indexTwoCharacter c).ker :=
  canonicalBasis.closure_range_indexTwoGenerators c

private theorem canonical_kernel_words (c : Fin 3) (g : F) :
    g ∈ (canonicalBasis.indexTwoCharacter c).ker ↔
      ∃ w : List (Fin 3 × Bool),
        FreeGroup.lift (canonicalBasis.indexTwoGenerators c) (FreeGroup.mk w) = g :=
  canonicalBasis.mem_indexTwoCharacter_ker_iff_exists_word c g

end FreeGroupBasis.IndexTwoExamples
