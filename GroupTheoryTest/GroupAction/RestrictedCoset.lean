/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.GroupAction.DoubleCoset
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Restricted cosets of a point stabilizer in the three-point permutation group

The point stabilizer of `2` in `Equiv.Perm (Fin 3)` is nonnormal. Its canonical action
on its left cosets has one fixed point and one orbit with two distinct points.
The model uses the tautological permutation action, the stock stabilizer subgroup,
and the canonical restricted quotient action. The model assertions do not assume the
double-coset or decomposition theorems; the final examples instantiate those APIs on
these same permutations and cosets.
-/

@[expose] public section

namespace ThreePointCosets

local notation "S₃" => Equiv.Perm (Fin 3)

/-- The subgroup fixing the last of three points, for the tautological permutation action. -/
def pointStabilizer : Subgroup S₃ := MulAction.stabilizer S₃ (2 : Fin 3)

/-- The transposition moving the distinguished point to `1`. -/
def crossing : S₃ := Equiv.swap 1 2

/-- The nonidentity permutation of the other two points, as an element of their stabilizer. -/
def flip : pointStabilizer := ⟨Equiv.swap 0 1, by
  change Equiv.swap (0 : Fin 3) 1 2 = 2
  decide⟩

/-- The identity coset. -/
def identityCoset : S₃ ⧸ pointStabilizer := QuotientGroup.mk (1 : S₃)

/-- The coset carrying the distinguished point to `1`. -/
def crossingCoset : S₃ ⧸ pointStabilizer := QuotientGroup.mk crossing

/-- A second point in the orbit of the crossing coset. -/
def thirdCoset : S₃ ⧸ pointStabilizer := flip • crossingCoset

/-- The chosen point stabilizer is not normal in the permutation group. -/
theorem pointStabilizer_not_normal : ¬ pointStabilizer.Normal := by
  intro hn
  have hconj := hn.conj_mem (flip : S₃) flip.property crossing
  have hnot : crossing * (flip : S₃) * crossing⁻¹ ∉ pointStabilizer := by
    change (crossing * (flip : S₃) * crossing⁻¹) (2 : Fin 3) ≠ 2
    decide
  exact hnot hconj

/-- All three displayed cosets are distinct. -/
theorem cosets_distinct : identityCoset ≠ crossingCoset ∧ identityCoset ≠ thirdCoset ∧
    crossingCoset ≠ thirdCoset := by
  let ev : (S₃ ⧸ pointStabilizer) → Fin 3 :=
    MulAction.ofQuotientStabilizer S₃ (2 : Fin 3)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv : (2 : Fin 3) = 1 := congrArg ev h
    exact (by decide : (2 : Fin 3) ≠ 1) hv
  · intro h
    have hv : (2 : Fin 3) = 0 := congrArg ev h
    exact (by decide : (2 : Fin 3) ≠ 0) hv
  · intro h
    have hv : (1 : Fin 3) = 0 := congrArg ev h
    exact (by decide : (1 : Fin 3) ≠ 0) hv

/-- The identity coset is fixed by the restricted action. -/
theorem smul_identityCoset (h : pointStabilizer) : h • identityCoset = identityCoset := by
  have h2 : (h : S₃) (2 : Fin 3) = 2 := h.property
  apply MulAction.injective_ofQuotientStabilizer S₃ (2 : Fin 3)
  exact (MulAction.ofQuotientStabilizer_smul S₃ (2 : Fin 3) (h : S₃)
    (QuotientGroup.mk (1 : S₃))).trans h2

/-- The other orbit consists of the two displayed distinct cosets. -/
theorem orbit_crossingCoset :
    MulAction.orbit pointStabilizer crossingCoset = {crossingCoset, thirdCoset} := by
  let ev : (S₃ ⧸ pointStabilizer) → Fin 3 :=
    MulAction.ofQuotientStabilizer S₃ (2 : Fin 3)
  have hinj : Function.Injective ev :=
    MulAction.injective_ofQuotientStabilizer S₃ (2 : Fin 3)
  have hev (h : pointStabilizer) : ev (h • crossingCoset) = (h : S₃) 1 := by
    exact MulAction.ofQuotientStabilizer_smul S₃ (2 : Fin 3) (h : S₃)
      (QuotientGroup.mk crossing)
  have hc : ev crossingCoset = 1 := by decide
  have ht : ev thirdCoset = 0 := by decide
  have cases_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  ext q
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, rfl⟩
    have h2 : (h : S₃) (2 : Fin 3) = 2 := h.property
    rcases cases_three ((h : S₃) 1) with h0 | h1 | h2'
    · exact Or.inr (hinj ((hev h).trans (h0.trans ht.symm)))
    · exact Or.inl (hinj ((hev h).trans (h1.trans hc.symm)))
    · have h12 : (1 : Fin 3) = 2 := (h : S₃).injective (h2'.trans h2.symm)
      exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h12)
  · rintro (rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · exact ⟨flip, rfl⟩

/-- The three displayed cosets exhaust the canonical quotient. -/
theorem coset_cases (q : S₃ ⧸ pointStabilizer) :
    q = identityCoset ∨ q = crossingCoset ∨ q = thirdCoset := by
  let ev : (S₃ ⧸ pointStabilizer) → Fin 3 :=
    MulAction.ofQuotientStabilizer S₃ (2 : Fin 3)
  have hinj : Function.Injective ev :=
    MulAction.injective_ofQuotientStabilizer S₃ (2 : Fin 3)
  have hi : ev identityCoset = 2 := rfl
  have hc : ev crossingCoset = 1 := by decide
  have ht : ev thirdCoset = 0 := by decide
  have cases_three : ∀ i : Fin 3, i = 2 ∨ i = 1 ∨ i = 0 := by decide
  rcases cases_three (ev q) with h2 | h1 | h0
  · exact Or.inl (hinj (h2.trans hi.symm))
  · exact Or.inr (Or.inl (hinj (h1.trans hc.symm)))
  · exact Or.inr (Or.inr (hinj (h0.trans ht.symm)))

/-- There are exactly two restricted orbit classes in this model. -/
theorem card_orbitRel_quotient :
    Nat.card (MulAction.orbitRel.Quotient pointStabilizer (S₃ ⧸ pointStabilizer)) = 2 := by
  let c₀ : MulAction.orbitRel.Quotient pointStabilizer (S₃ ⧸ pointStabilizer) :=
    _root_.Quotient.mk _ identityCoset
  let c₁ : MulAction.orbitRel.Quotient pointStabilizer (S₃ ⧸ pointStabilizer) :=
    _root_.Quotient.mk _ crossingCoset
  apply Nat.card_eq_two_iff.mpr
  refine ⟨c₀, c₁, ?_, ?_⟩
  · intro h
    have hm : identityCoset ∈ MulAction.orbit pointStabilizer crossingCoset :=
      _root_.Quotient.exact h
    rw [orbit_crossingCoset] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact hm.elim cosets_distinct.1 cosets_distinct.2.1
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    refine _root_.Quotient.inductionOn z ?_
    intro q
    rcases coset_cases q with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr
        (MulAction.orbitRel.Quotient.quotient_smul_eq (g := flip) (a := crossingCoset))

/-- The two-point orbit has trivial stabilizer inside the acting point stabilizer. -/
theorem stabilizer_crossingCoset : MulAction.stabilizer pointStabilizer crossingCoset = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro h hh
  change h = 1
  have h2 : (h : S₃) (2 : Fin 3) = 2 := h.property
  have h1 : (h : S₃) (1 : Fin 3) = 1 := by
    have hv := congrArg (MulAction.ofQuotientStabilizer S₃ (2 : Fin 3))
      (MulAction.mem_stabilizer_iff.mp hh)
    exact (MulAction.ofQuotientStabilizer_smul S₃ (2 : Fin 3) (h : S₃)
      (QuotientGroup.mk crossing)).symm.trans hv
  have cases_three : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  have h0 : (h : S₃) (0 : Fin 3) = 0 := by
    rcases cases_three ((h : S₃) 0) with h0 | h1' | h2'
    · exact h0
    · have h01 : (0 : Fin 3) = 1 := (h : S₃).injective (h1'.trans h1.symm)
      exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h01)
    · have h02 : (0 : Fin 3) = 2 := (h : S₃).injective (h2'.trans h2.symm)
      exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h02)
  apply Subtype.ext
  apply Equiv.ext
  intro i
  rcases cases_three i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

example :
    MulAction.orbitQuotientQuotientEquivDoubleCoset pointStabilizer pointStabilizer
        (_root_.Quotient.mk (MulAction.orbitRel pointStabilizer (S₃ ⧸ pointStabilizer))
          crossingCoset) = DoubleCoset.mk pointStabilizer pointStabilizer crossing :=
  MulAction.orbitQuotientQuotientEquivDoubleCoset_apply_mk pointStabilizer pointStabilizer crossing

example :
    (MulAction.orbitQuotientQuotientEquivDoubleCoset pointStabilizer pointStabilizer).symm
        (DoubleCoset.mk pointStabilizer pointStabilizer crossing) =
      _root_.Quotient.mk (MulAction.orbitRel pointStabilizer (S₃ ⧸ pointStabilizer))
        crossingCoset :=
  MulAction.orbitQuotientQuotientEquivDoubleCoset_symm_apply_mk
    pointStabilizer pointStabilizer crossing

example : MulAction.stabilizer pointStabilizer crossingCoset =
    (pointStabilizer.map (MulAut.conj crossing).toMonoidHom).comap pointStabilizer.subtype :=
  MulAction.stabilizer_subgroup_quotient pointStabilizer pointStabilizer crossing

example :
    ((MulAction.orbitEquivQuotientStabilizer pointStabilizer crossingCoset).symm
      (QuotientGroup.mk flip) : S₃ ⧸ pointStabilizer) = thirdCoset :=
  rfl

example :
    (MulAction.orbitEquivQuotientStabilizer pointStabilizer crossingCoset).symm
        (flip • QuotientGroup.mk (1 : pointStabilizer)) =
      flip • (MulAction.orbitEquivQuotientStabilizer pointStabilizer crossingCoset).symm
        (QuotientGroup.mk (1 : pointStabilizer)) :=
  MulAction.orbitEquivQuotientStabilizer_symm_smul crossingCoset flip
    (QuotientGroup.mk (1 : pointStabilizer))

example :
    (MulAction.quotientEquivSigmaDoubleCoset pointStabilizer pointStabilizer crossingCoset).2.val =
      crossingCoset :=
  MulAction.quotientEquivSigmaDoubleCoset_apply_snd pointStabilizer pointStabilizer crossingCoset

example :
    MulAction.quotientEquivSigmaDoubleCoset pointStabilizer pointStabilizer (flip • crossingCoset) =
      flip • MulAction.quotientEquivSigmaDoubleCoset pointStabilizer pointStabilizer
        crossingCoset :=
  MulAction.quotientEquivSigmaDoubleCoset_smul pointStabilizer pointStabilizer flip crossingCoset

end ThreePointCosets
