/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.GroupAction.Automorphism
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Bool

/-!
# Clients for transitive-action automorphisms

The regular `S₃` action detects the order of composition using `(01)` and `(12)`.
The natural `S₃` action on three points has a nonnormal stabilizer, so it does
not fall under the finite-normal coset construction. Finally, the trivial action
on `Bool` has a nontrivial equivariant swap but a trivial normalizer quotient:
transitivity cannot be omitted.
-/

open CategoryTheory

private abbrev S3 := Equiv.Perm (Fin 3)

-- These hypotheses and the noncommutativity check do not use the classification.
example : MulAction.IsPretransitive S3 S3 := inferInstance

example : MulAction.stabilizer S3 (1 : S3) = ⊥ :=
  IsCancelSMul.stabilizer_eq_bot 1

private theorem swaps_do_not_commute :
    (Equiv.swap (0 : Fin 3) 1 : S3) * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap 0 1 := by decide

private def regularParameter (p : S3) :
    Subgroup.normalizer (MulAction.stabilizer S3 (1 : S3) : Set S3) :=
  ⟨p, by
    rw [IsCancelSMul.stabilizer_eq_bot, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top p⟩

/-- The regular classification sends `(01)(12)` to the inverse right translation:
at the identity, the resulting permutation sends `0` to `2`, not `1`. -/
private theorem regular_composition_orientation :
    let n := regularParameter (Equiv.swap 0 1)
    let m := regularParameter (Equiv.swap 1 2)
    let e := MulAction.normalizerQuotientEquivAut (G := S3) (1 : S3)
    ((show S3 from (e (QuotientGroup.mk n) * e (QuotientGroup.mk m)).hom.hom (1 : S3)) 0 = 2) ∧
      ((show S3 from (e (QuotientGroup.mk m) * e (QuotientGroup.mk n)).hom.hom (1 : S3)) 0 = 1) := by
  dsimp only
  rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  simp only [MulAction.normalizerQuotientEquivAut_mk_apply_self]
  decide

/-- The full permutation action is transitive, independently of the classification. -/
private theorem three_point_pretransitive : MulAction.IsPretransitive S3 (Fin 3) where
  exists_smul_eq i j := ⟨Equiv.swap i j, Equiv.swap_apply_left i j⟩

/-- The stabilizer of `0` in the natural `S₃` action is not normal:
conjugating `(12)` by `(01)` moves `0`. -/
private theorem three_point_stabilizer_not_normal :
    ¬ (MulAction.stabilizer S3 (0 : Fin 3)).Normal := by
  intro h
  have hmem : (Equiv.swap (1 : Fin 3) 2 : S3) ∈
      MulAction.stabilizer S3 (0 : Fin 3) := by decide
  have hconj := h.conj_mem _ hmem (Equiv.swap 0 1)
  exact (by decide :
    (Equiv.swap (0 : Fin 3) 1 : S3) * Equiv.swap 1 2 * (Equiv.swap 0 1)⁻¹ ∉
      MulAction.stabilizer S3 (0 : Fin 3)) hconj

/-- A concrete use of the classification with a nonnormal point stabilizer. -/
private theorem three_point_classification :
    let n : Subgroup.normalizer (MulAction.stabilizer S3 (0 : Fin 3) : Set S3) :=
      ⟨Equiv.swap 1 2, Subgroup.le_normalizer (by decide)⟩
    (MulAction.normalizerQuotientEquivAut (G := S3) (0 : Fin 3)
      (QuotientGroup.mk n)).hom.hom (0 : Fin 3) = (0 : Fin 3) := by
  dsimp only
  rw [MulAction.normalizerQuotientEquivAut_mk_apply_self]
  exact (by decide : (Equiv.swap (1 : Fin 3) 2 : S3)⁻¹ (0 : Fin 3) = 0)

section Nontransitive

local instance : MulAction Unit Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def boolSwap : Aut (Action.ofMulAction Unit Bool) :=
  Action.mkIso Equiv.boolNot.toIso fun _ => by
    ext b
    rfl

/-- Failure of transitivity and the obstruction to the classification hold
without using any of its declarations. The source quotient is trivial whereas
the target contains the nonidentity equivariant Boolean swap. -/
private theorem nontransitive_boundary :
    ¬ MulAction.IsPretransitive Unit Bool ∧
      Subsingleton (Subgroup.normalizer (MulAction.stabilizer Unit false : Set Unit) ⧸
        (MulAction.stabilizer Unit false).subgroupOf
          (Subgroup.normalizer (MulAction.stabilizer Unit false : Set Unit))) ∧
      boolSwap ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨g, hg⟩ := h.exists_smul_eq false true
    exact Bool.false_ne_true hg
  · apply QuotientGroup.subsingleton_iff.mpr
    apply Subgroup.subgroupOf_eq_top.mpr
    intro g _
    exact Subsingleton.elim (g : Unit) 1 ▸ (MulAction.stabilizer Unit false).one_mem
  · intro h
    have hvalue := congrArg (fun a : Aut (Action.ofMulAction Unit Bool) => a.hom.hom false) h
    exact Bool.false_ne_true hvalue.symm

end Nontransitive
