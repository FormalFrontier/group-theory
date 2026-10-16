/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.GroupAction.Centralizer
import GroupTheory.GroupAction.Automorphism
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# Centralizer transitivity and normal point stabilizers

The centralizer criterion is applied in both directions to translation through
the first projection from `C₂ × C₂` to `C₂`, whose stabilizer is proper, nontrivial
and normal and whose action is nonfaithful. Independent translation witnesses
establish centralizer pretransitivity. The natural `S₃` action has a nonnormal
stabilizer. A singleton permits pretransitive commuting scalars without monoid laws.
-/

set_option linter.privateModule false

@[expose] public section

universe u v

example {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (c : Subgroup.centralizer (Set.range (MulAction.toPermHom G X))) (y : X) :
    c • y = (c : Equiv.Perm X) y := rfl

end

section ProjectionTranslation

local notation "C₂" => Multiplicative (ZMod 2)
local notation "Γ" => C₂ × C₂
local notation "ε" => Multiplicative.ofAdd (1 : ZMod 2)

local instance : MulAction Γ C₂ :=
  MulAction.compHom C₂ (MonoidHom.fst C₂ C₂)

local instance : MulAction.IsPretransitive Γ C₂ :=
  MulAction.isPretransitive_compHom
    (f := MonoidHom.fst C₂ C₂) (fun a => ⟨(a, 1), rfl⟩)

-- The second factor supplies a nonidentity stabilizer element; the first factor
-- supplies an element outside the stabilizer.
private theorem projection_stabilizer_data :
    (MulAction.stabilizer Γ (1 : C₂)).Normal ∧
      ((1, ε) : Γ) ∈ MulAction.stabilizer Γ (1 : C₂) ∧
      ((1, ε) : Γ) ≠ 1 ∧
      ((ε, 1) : Γ) ∉ MulAction.stabilizer Γ (1 : C₂) := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩ <;> decide

example : ¬ FaithfulSMul Γ C₂ := by
  intro h
  have heq : ((1, ε) : Γ) = 1 :=
    h.eq_of_smul_eq_smul (fun _ => rfl)
  exact (by decide : ((1, ε) : Γ) ≠ 1) heq

-- Regular C₂ translations independently give centralizing permutations.
private theorem projection_centralizer_pretransitive : MulAction.IsPretransitive
    (Subgroup.centralizer (Set.range (MulAction.toPermHom Γ C₂))) C₂ where
  exists_smul_eq x y := by
    refine ⟨⟨MulAction.toPerm (y * x⁻¹), ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, rfl⟩
      ext z
      change g.1 * ((y * x⁻¹) * z) = (y * x⁻¹) * (g.1 * z)
      exact mul_left_comm _ _ _
    · change (y * x⁻¹) * x = y
      exact inv_mul_cancel_right _ _

example : (MulAction.stabilizer Γ (1 : C₂)).Normal :=
  (MulAction.isPretransitive_centralizer_iff_stabilizer_normal (G := Γ) (1 : C₂)).mp
    projection_centralizer_pretransitive

example : MulAction.IsPretransitive
    (Subgroup.centralizer (Set.range (MulAction.toPermHom Γ C₂))) C₂ :=
  (MulAction.isPretransitive_centralizer_iff_stabilizer_normal (G := Γ) (1 : C₂)).mpr
    projection_stabilizer_data.1

end ProjectionTranslation

section ThreePoints

local notation "S₃" => Equiv.Perm (Fin 3)

example : MulAction.IsPretransitive S₃ (Fin 3) := inferInstance

-- As in the automorphism tests, conjugating (12) by (01) moves 0.
private theorem three_point_stabilizer_not_normal :
    ¬ (MulAction.stabilizer S₃ (0 : Fin 3)).Normal := by
  intro h
  have hmem : (Equiv.swap (1 : Fin 3) 2 : S₃) ∈
      MulAction.stabilizer S₃ (0 : Fin 3) := by decide
  have hconj := h.conj_mem _ hmem (Equiv.swap 0 1)
  exact (by decide :
    (Equiv.swap (0 : Fin 3) 1 : S₃) * Equiv.swap 1 2 * (Equiv.swap 0 1)⁻¹ ∉
      MulAction.stabilizer S₃ (0 : Fin 3)) hconj

example : ¬ MulAction.IsPretransitive
    (Subgroup.centralizer (Set.range (MulAction.toPermHom S₃ (Fin 3)))) (Fin 3) := by
  intro h
  exact three_point_stabilizer_not_normal
    ((MulAction.isPretransitive_centralizer_iff_stabilizer_normal (G := S₃) (0 : Fin 3)).mp h)

end ThreePoints

section Singleton

local instance : SMul (Fin 2) Unit where
  smul _ _ := ()

local instance : SMulCommClass Unit (Fin 2) Unit where
  smul_comm _ _ _ := Subsingleton.elim _ _

local instance : MulAction.IsPretransitive (Fin 2) Unit where
  exists_smul_eq _ _ := ⟨0, Subsingleton.elim _ _⟩

-- No monoid structure on Fin 2 is needed for the commuting-scalar theorem.
example : (MulAction.stabilizer Unit ()).Normal :=
  MulAction.stabilizer_normal_of_pretransitive_commuting (G := Unit) (H := Fin 2) ()

example : (MulAction.stabilizer Unit ()).Normal := inferInstance

example : MulAction.IsPretransitive
    (Subgroup.centralizer (Set.range (MulAction.toPermHom Unit Unit))) Unit := inferInstance

end Singleton
