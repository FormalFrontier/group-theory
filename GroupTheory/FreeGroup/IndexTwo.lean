/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Subgroup.IndexTwo
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Index-two characters and generators from a two-element free group basis

A free group basis defines three nontrivial characters to the two-element
cyclic group. Their kernels are the three index-two subgroups. Explicit triples
generate these kernels; freeness of the triples is not asserted.

The two-generator application is J. P. May, *A Concise Course in Algebraic
Topology*, Chapter 4, Problem 1, p. 38. Mathlib's `FreeGroupBasis` supplies the
basis and lift APIs; its Schreier generators supply the subgroup-spanning argument.
-/

@[expose] public section

universe u

namespace FreeGroupBasis

variable {G : Type u} [Group G]

local notation "indexTwoCoefficients" =>
  (![![Multiplicative.ofAdd 1, 1], ![1, Multiplicative.ofAdd 1],
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]] :
      Fin 3 → Fin 2 → Multiplicative (ZMod 2))

/-- The characters with generator values `10`, `01`, and `11`, in that order. -/
def indexTwoCharacter (b : FreeGroupBasis (Fin 2) G) (c : Fin 3) :
    G →* Multiplicative (ZMod 2) :=
  b.lift (indexTwoCoefficients c)

/-- Explicit generators for the three character kernels, in the order `10`, `01`, `11`. -/
def indexTwoGenerators (b : FreeGroupBasis (Fin 2) G) (c : Fin 3) : Fin 3 → G :=
  ![![b 0 ^ 2, b 1, b 0 * b 1 * (b 0)⁻¹],
    ![b 1 ^ 2, b 0, b 1 * b 0 * (b 1)⁻¹],
    ![b 0 ^ 2, b 1 * (b 0)⁻¹, b 0 * b 1]] c

variable (b : FreeGroupBasis (Fin 2) G)

@[simp]
theorem indexTwoCharacter_zero_apply_zero :
    b.indexTwoCharacter 0 (b 0) = Multiplicative.ofAdd (1 : ZMod 2) := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 0)) 0

@[simp]
theorem indexTwoCharacter_zero_apply_one : b.indexTwoCharacter 0 (b 1) = 1 := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 0)) 1

@[simp]
theorem indexTwoCharacter_one_apply_zero : b.indexTwoCharacter 1 (b 0) = 1 := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 1)) 0

@[simp]
theorem indexTwoCharacter_one_apply_one :
    b.indexTwoCharacter 1 (b 1) = Multiplicative.ofAdd (1 : ZMod 2) := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 1)) 1

@[simp]
theorem indexTwoCharacter_two_apply_zero :
    b.indexTwoCharacter 2 (b 0) = Multiplicative.ofAdd (1 : ZMod 2) := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 2)) 0

@[simp]
theorem indexTwoCharacter_two_apply_one :
    b.indexTwoCharacter 2 (b 1) = Multiplicative.ofAdd (1 : ZMod 2) := by
  exact congrFun (b.lift.symm_apply_apply (indexTwoCoefficients 2)) 1

@[simp]
theorem indexTwoGenerators_zero_apply_zero : b.indexTwoGenerators 0 0 = b 0 ^ 2 := rfl

@[simp]
theorem indexTwoGenerators_zero_apply_one : b.indexTwoGenerators 0 1 = b 1 := rfl

@[simp]
theorem indexTwoGenerators_zero_apply_two :
    b.indexTwoGenerators 0 2 = b 0 * b 1 * (b 0)⁻¹ := rfl

@[simp]
theorem indexTwoGenerators_one_apply_zero : b.indexTwoGenerators 1 0 = b 1 ^ 2 := rfl

@[simp]
theorem indexTwoGenerators_one_apply_one : b.indexTwoGenerators 1 1 = b 0 := rfl

@[simp]
theorem indexTwoGenerators_one_apply_two :
    b.indexTwoGenerators 1 2 = b 1 * b 0 * (b 1)⁻¹ := rfl

@[simp]
theorem indexTwoGenerators_two_apply_zero : b.indexTwoGenerators 2 0 = b 0 ^ 2 := rfl

@[simp]
theorem indexTwoGenerators_two_apply_one :
    b.indexTwoGenerators 2 1 = b 1 * (b 0)⁻¹ := rfl

@[simp]
theorem indexTwoGenerators_two_apply_two : b.indexTwoGenerators 2 2 = b 0 * b 1 := rfl

/-- The two basis elements generate the ambient group. -/
theorem closure_pair_eq_top : Subgroup.closure ({b 0, b 1} : Set G) = ⊤ := by
  have hlift : FreeGroup.lift (b : Fin 2 → G) = b.repr.symm.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of]
    rfl
  have hgen : Subgroup.closure (Set.range (b : Fin 2 → G)) = ⊤ :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mp (by
      rw [hlift]
      exact b.repr.symm.surjective)
  have hrange : Set.range (b : Fin 2 → G) = {b 0, b 1} := by
    rw [← Matrix.range_cons_cons_empty (b 0) (b 1) ![]]
    congr 1
    funext i
    fin_cases i <;> rfl
  rwa [hrange] at hgen

/-- Each of the three displayed characters is nontrivial. -/
theorem indexTwoCharacter_ne_one (c : Fin 3) : b.indexTwoCharacter c ≠ 1 := by
  fin_cases c
  · intro h
    have hzero := DFunLike.congr_fun h (b 0)
    simp at hzero
  · intro h
    have hone := DFunLike.congr_fun h (b 1)
    simp at hone
  · intro h
    have hzero := DFunLike.congr_fun h (b 0)
    simp at hzero

/-- Each of the three displayed characters is surjective. -/
theorem indexTwoCharacter_surjective (c : Fin 3) :
    Function.Surjective (b.indexTwoCharacter c) := by
  intro y
  have hvalues : ∀ z : Multiplicative (ZMod 2),
      z = 1 ∨ z = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  rcases hvalues y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · fin_cases c
    · exact ⟨b 0, b.indexTwoCharacter_zero_apply_zero⟩
    · exact ⟨b 1, b.indexTwoCharacter_one_apply_one⟩
    · exact ⟨b 0, b.indexTwoCharacter_two_apply_zero⟩

/-- Each displayed character has an index-two kernel. -/
theorem indexTwoCharacter_ker_index (c : Fin 3) : (b.indexTwoCharacter c).ker.index = 2 := by
  exact (MonoidHom.ker_index_eq_two_iff
    (by simp [Nat.card_eq_fintype_card]) (b.indexTwoCharacter c)).mpr
      (b.indexTwoCharacter_ne_one c)

/-- The three displayed characters are pairwise distinct. -/
theorem indexTwoCharacter_injective : Function.Injective b.indexTwoCharacter := by
  have hcoeff : Function.Injective indexTwoCoefficients := by decide
  intro c d h
  exact hcoeff (b.lift.injective h)

/-- The three character kernels are pairwise distinct. -/
theorem indexTwoCharacter_ker_injective :
    Function.Injective (fun c : Fin 3 ↦ (b.indexTwoCharacter c).ker) := by
  exact (MonoidHom.ker_injective_of_card_eq_two
    (by simp [Nat.card_eq_fintype_card])).comp b.indexTwoCharacter_injective

/-- The displayed characters uniquely exhaust the nontrivial characters. -/
theorem ne_one_iff_existsUnique_indexTwoCharacter (χ : G →* Multiplicative (ZMod 2)) :
    χ ≠ 1 ↔ ∃! c : Fin 3, χ = b.indexTwoCharacter c := by
  constructor
  · intro hχ
    have hvalues : ∀ z : Multiplicative (ZMod 2),
        z = 1 ∨ z = Multiplicative.ofAdd (1 : ZMod 2) := by decide
    obtain ⟨c, hc⟩ : ∃ c : Fin 3, χ = b.indexTwoCharacter c := by
      rcases hvalues (χ (b 0)) with hzero | hzero <;>
        rcases hvalues (χ (b 1)) with hone | hone
      · exact (hχ (b.ext_hom χ 1 (by
          intro i
          fin_cases i <;> simpa using (by assumption)))).elim
      · refine ⟨1, b.ext_hom χ (b.indexTwoCharacter 1) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
      · refine ⟨0, b.ext_hom χ (b.indexTwoCharacter 0) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
      · refine ⟨2, b.ext_hom χ (b.indexTwoCharacter 2) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact b.indexTwoCharacter_injective (hd.symm.trans hc)
  · rintro ⟨c, hc, _⟩
    rw [hc]
    exact b.indexTwoCharacter_ne_one c

/-- The displayed character kernels uniquely exhaust the index-two subgroups. -/
theorem index_eq_two_iff_existsUnique_indexTwoCharacter_ker (H : Subgroup G) :
    H.index = 2 ↔ ∃! c : Fin 3, H = (b.indexTwoCharacter c).ker := by
  constructor
  · intro hH
    obtain ⟨c, hc, _⟩ :=
      (b.ne_one_iff_existsUnique_indexTwoCharacter (H.characterOfIndexTwo hH)).mp
        (H.characterOfIndexTwo_ne_one hH)
    have hker : H = (b.indexTwoCharacter c).ker := by
      rw [← H.ker_characterOfIndexTwo hH, hc]
    refine ⟨c, hker, ?_⟩
    intro d hd
    exact b.indexTwoCharacter_ker_injective (hd.symm.trans hker)
  · rintro ⟨c, rfl, _⟩
    exact b.indexTwoCharacter_ker_index c

/-- Every displayed generator belongs to its specified character kernel. -/
theorem indexTwoGenerators_mem_ker (c j : Fin 3) :
    b.indexTwoGenerators c j ∈ (b.indexTwoCharacter c).ker := by
  fin_cases c <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, indexTwoGenerators_zero_apply_zero, MonoidHom.mem_ker,
      map_pow, indexTwoCharacter_zero_apply_zero]
    decide
  · simp [MonoidHom.mem_ker]
  · simp [MonoidHom.mem_ker, map_mul, map_inv]
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, indexTwoGenerators_one_apply_zero,
      MonoidHom.mem_ker, map_pow, indexTwoCharacter_one_apply_one]
    decide
  · simp [MonoidHom.mem_ker]
  · simp [MonoidHom.mem_ker, map_mul, map_inv]
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.zero_eta, indexTwoGenerators_two_apply_zero,
      MonoidHom.mem_ker, map_pow, indexTwoCharacter_two_apply_zero]
    decide
  · simp [MonoidHom.mem_ker, map_mul, map_inv]
  · simp only [Fin.reduceFinMk, Fin.isValue, indexTwoGenerators_two_apply_two, MonoidHom.mem_ker,
      map_mul, indexTwoCharacter_two_apply_zero, indexTwoCharacter_two_apply_one]
    decide

/-- The displayed words genuinely generate the specified character kernel. -/
theorem closure_range_indexTwoGenerators (c : Fin 3) :
    Subgroup.closure (Set.range (b.indexTwoGenerators c)) = (b.indexTwoCharacter c).ker := by
  fin_cases c
  · change Subgroup.closure (Set.range ![b 0 ^ 2, b 1, b 0 * b 1 * (b 0)⁻¹]) =
      (b.indexTwoCharacter 0).ker
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using
      Subgroup.closure_sq_pair_conj_eq_of_index_eq_two
        (b.indexTwoCharacter 0).ker (b.indexTwoCharacter_ker_index 0) (b 0) (b 1)
        b.closure_pair_eq_top (by simp [MonoidHom.mem_ker]) (by simp [MonoidHom.mem_ker])
  · change Subgroup.closure (Set.range ![b 1 ^ 2, b 0, b 1 * b 0 * (b 1)⁻¹]) =
      (b.indexTwoCharacter 1).ker
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using
      Subgroup.closure_sq_pair_conj_eq_of_index_eq_two
        (b.indexTwoCharacter 1).ker (b.indexTwoCharacter_ker_index 1) (b 1) (b 0)
        (by simpa [Set.pair_comm] using b.closure_pair_eq_top)
        (by simp [MonoidHom.mem_ker]) (by simp [MonoidHom.mem_ker])
  · change Subgroup.closure (Set.range ![b 0 ^ 2, b 1 * (b 0)⁻¹, b 0 * b 1]) =
      (b.indexTwoCharacter 2).ker
    simpa only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using
      Subgroup.closure_sq_pair_mul_eq_of_index_eq_two
        (b.indexTwoCharacter 2).ker (b.indexTwoCharacter_ker_index 2) (b 0) (b 1)
        b.closure_pair_eq_top (by simp [MonoidHom.mem_ker]) (by simp [MonoidHom.mem_ker])

/-- Kernel membership is equivalent to evaluation of a word in the displayed generators. -/
theorem mem_indexTwoCharacter_ker_iff_exists_word (c : Fin 3) (g : G) :
    g ∈ (b.indexTwoCharacter c).ker ↔
      ∃ w : List (Fin 3 × Bool), FreeGroup.lift (b.indexTwoGenerators c) (FreeGroup.mk w) = g := by
  rw [← b.closure_range_indexTwoGenerators c, ← FreeGroup.range_lift_eq_closure]
  change (∃ x : FreeGroup (Fin 3), FreeGroup.lift (b.indexTwoGenerators c) x = g) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    rcases x with ⟨w⟩
    exact ⟨w, hx⟩
  · rintro ⟨w, hw⟩
    exact ⟨FreeGroup.mk w, hw⟩

end FreeGroupBasis
