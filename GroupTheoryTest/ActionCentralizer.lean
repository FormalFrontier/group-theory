/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.GroupAction.Centralizer
import Mathlib.GroupTheory.Perm.Fin

/-!
# Automorphisms of actions and centralizers

The canonical centralizer equivalences act on two independently constructed,
noncommuting equivariant swaps of the trivial action on three points. The same
constructors and their inverse API also apply to the empty type without a chosen point.
-/

open CategoryTheory

universe u

set_option linter.privateModule false

section ThreePoints

variable (G : Type u) [Group G]

private abbrev threePointTrivialAction : MulAction G (Fin 3) :=
  MulAction.ofEndHom (1 : G →* Function.End (Fin 3))

attribute [local instance] threePointTrivialAction

private def swapZeroOne : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def swapOneTwo : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private def swapZeroOneAut : Aut (Action.ofMulAction G (Fin 3)) :=
  Action.mkIso swapZeroOne.toIso fun _ => by
    ext x
    rfl

private def swapOneTwoAut : Aut (Action.ofMulAction G (Fin 3)) :=
  Action.mkIso swapOneTwo.toIso fun _ => by
    ext x
    rfl

private theorem threePoint_action_perm (g : G) :
    MulAction.toPermHom G (Fin 3) g = 1 := by
  ext x
  rfl

private def swapZeroOneCentralizer :
    Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3))) :=
  ⟨swapZeroOne, by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    rw [threePoint_action_perm]
    simp⟩

private def swapOneTwoCentralizer :
    Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3))) :=
  ⟨swapOneTwo, by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    rw [threePoint_action_perm]
    simp⟩

private def swapZeroOneIsoCentralizer :
    Subgroup.centralizer (Set.range (Action.ofMulAction G (Fin 3)).ρAut) :=
  ⟨Aut.mulEquivPerm.symm swapZeroOne, by
    change Aut.mulEquivPerm.symm swapZeroOne ∈
      (Subgroup.centralizer (Set.range (Action.ofMulAction G (Fin 3)).ρAut) :
        Subgroup (Aut (Fin 3)))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    apply Aut.ext
    ext x
    rfl⟩

private def swapOneTwoIsoCentralizer :
    Subgroup.centralizer (Set.range (Action.ofMulAction G (Fin 3)).ρAut) :=
  ⟨Aut.mulEquivPerm.symm swapOneTwo, by
    change Aut.mulEquivPerm.symm swapOneTwo ∈
      (Subgroup.centralizer (Set.range (Action.ofMulAction G (Fin 3)).ρAut) :
        Subgroup (Aut (Fin 3)))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    apply Aut.ext
    ext x
    rfl⟩

private theorem threePoint_underlying_agreement :
    (Action.forget (Type 0) G).mapIso (swapZeroOneAut G) =
        (swapZeroOneIsoCentralizer G).val ∧
      (Action.forget (Type 0) G).mapIso (swapOneTwoAut G) =
        (swapOneTwoIsoCentralizer G).val ∧
      Aut.mulEquivPerm (α := Fin 3) ((Action.forget (Type 0) G).mapIso (swapZeroOneAut G)) =
        (swapZeroOneCentralizer G : Equiv.Perm (Fin 3)) ∧
      Aut.mulEquivPerm (α := Fin 3) ((Action.forget (Type 0) G).mapIso (swapOneTwoAut G)) =
        (swapOneTwoCentralizer G : Equiv.Perm (Fin 3)) :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem threePoint_nonidentity :
    swapZeroOneAut G ≠ 1 ∧ swapOneTwoAut G ≠ 1 ∧
      swapZeroOneCentralizer G ≠ 1 ∧ swapOneTwoCentralizer G ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hx : (1 : Fin 3) = 0 :=
      congrArg (fun a : Aut (Action.ofMulAction G (Fin 3)) => a.hom.hom (0 : Fin 3)) h
    exact (by decide : (1 : Fin 3) ≠ 0) hx
  · intro h
    have hx : (2 : Fin 3) = 1 :=
      congrArg (fun a : Aut (Action.ofMulAction G (Fin 3)) => a.hom.hom (1 : Fin 3)) h
    exact (by decide : (2 : Fin 3) ≠ 1) hx
  · intro h
    have hx : (1 : Fin 3) = 0 :=
      congrArg (fun f : Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3))) =>
        (f : Equiv.Perm (Fin 3)) 0) h
    exact (by decide : (1 : Fin 3) ≠ 0) hx
  · intro h
    have hx : (2 : Fin 3) = 1 :=
      congrArg (fun f : Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3))) =>
        (f : Equiv.Perm (Fin 3)) 1) h
    exact (by decide : (2 : Fin 3) ≠ 1) hx

private theorem threePoint_composition :
    (swapZeroOneAut G * swapOneTwoAut G).hom.hom (0 : Fin 3) = (1 : Fin 3) ∧
      (swapOneTwoAut G * swapZeroOneAut G).hom.hom (0 : Fin 3) = (2 : Fin 3) ∧
      ((swapZeroOneCentralizer G * swapOneTwoCentralizer G :
        Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3)))) :
          Equiv.Perm (Fin 3)) 0 = 1 ∧
      ((swapOneTwoCentralizer G * swapZeroOneCentralizer G :
        Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3)))) :
          Equiv.Perm (Fin 3)) 0 = 2 ∧
      (swapZeroOneAut G * swapOneTwoAut G).inv.hom (0 : Fin 3) = (2 : Fin 3) ∧
      (((swapZeroOneCentralizer G * swapOneTwoCentralizer G :
        Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3)))) :
          Equiv.Perm (Fin 3)).symm 0) = 2 ∧
      (swapOneTwoAut G).hom.hom (0 : Fin 3) = (0 : Fin 3) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem threePoint_noncommutative :
    swapZeroOneAut G * swapOneTwoAut G ≠ swapOneTwoAut G * swapZeroOneAut G ∧
      swapZeroOneCentralizer G * swapOneTwoCentralizer G ≠
        swapOneTwoCentralizer G * swapZeroOneCentralizer G := by
  constructor
  · intro h
    have hx : (1 : Fin 3) = 2 :=
      congrArg (fun a : Aut (Action.ofMulAction G (Fin 3)) => a.hom.hom (0 : Fin 3)) h
    exact (by decide : (1 : Fin 3) ≠ 2) hx
  · intro h
    have hx : (1 : Fin 3) = 2 :=
      congrArg (fun f : Subgroup.centralizer (Set.range (MulAction.toPermHom G (Fin 3))) =>
        (f : Equiv.Perm (Fin 3)) 0) h
    exact (by decide : (1 : Fin 3) ≠ 2) hx

private theorem threePoint_generic_forward :
    Action.autEquivCentralizer (Action.ofMulAction G (Fin 3)) (swapZeroOneAut G) =
        swapZeroOneIsoCentralizer G ∧
      Action.autEquivCentralizer (Action.ofMulAction G (Fin 3)) (swapOneTwoAut G) =
        swapOneTwoIsoCentralizer G := by
  constructor <;> apply Subtype.ext <;> rw [Action.coe_autEquivCentralizer]
  · exact (threePoint_underlying_agreement G).1
  · exact (threePoint_underlying_agreement G).2.1

private theorem threePoint_generic_inverse :
    (Action.autEquivCentralizer (Action.ofMulAction G (Fin 3))).symm
        (swapZeroOneIsoCentralizer G) = swapZeroOneAut G := by
  apply Aut.ext
  apply Action.hom_ext
  exact congrArg Iso.hom (Action.mapIso_autEquivCentralizer_symm
    (Action.ofMulAction G (Fin 3)) (swapZeroOneIsoCentralizer G))

private theorem threePoint_concrete_forward :
    Action.autEquivPermCentralizer G (Fin 3) (swapZeroOneAut G) =
        swapZeroOneCentralizer G ∧
      Action.autEquivPermCentralizer G (Fin 3) (swapOneTwoAut G) =
        swapOneTwoCentralizer G := by
  constructor <;> apply (Action.autEquivPermCentralizer_eq_iff G (Fin 3) _ _).2
  all_goals intro x; rfl

private theorem threePoint_concrete_inverse :
    (Action.autEquivPermCentralizer G (Fin 3)).symm (swapZeroOneCentralizer G) =
        swapZeroOneAut G := by
  apply Aut.ext
  apply Action.hom_ext
  ext x
  exact Action.autEquivPermCentralizer_symm_hom_apply G (Fin 3)
    (swapZeroOneCentralizer G) x

private theorem threePoint_canonical_product :
    Action.autEquivPermCentralizer G (Fin 3) (swapZeroOneAut G * swapOneTwoAut G) =
        swapZeroOneCentralizer G * swapOneTwoCentralizer G ∧
      Action.autEquivCentralizer (Action.ofMulAction G (Fin 3))
          (swapZeroOneAut G * swapOneTwoAut G) =
        swapZeroOneIsoCentralizer G * swapOneTwoIsoCentralizer G := by
  constructor
  · rw [map_mul, (threePoint_concrete_forward G).1, (threePoint_concrete_forward G).2]
  · rw [map_mul, (threePoint_generic_forward G).1, (threePoint_generic_forward G).2]

private theorem threePoint_canonical_coordinates :
    (Action.autEquivPermCentralizer G (Fin 3)
        (swapZeroOneAut G * swapOneTwoAut G) : Equiv.Perm (Fin 3)) 0 = 1 ∧
      (Action.autEquivPermCentralizer G (Fin 3)
        (swapOneTwoAut G * swapZeroOneAut G) : Equiv.Perm (Fin 3)) 0 = 2 ∧
      (Action.autEquivPermCentralizer G (Fin 3)
        (swapZeroOneAut G * swapOneTwoAut G) : Equiv.Perm (Fin 3)).symm 0 = 2 ∧
      ((Action.autEquivPermCentralizer G (Fin 3)).symm
        (swapZeroOneCentralizer G * swapOneTwoCentralizer G)).hom.hom (0 : Fin 3) = (1 : Fin 3) ∧
      ((Action.autEquivPermCentralizer G (Fin 3)).symm
        (swapZeroOneCentralizer G * swapOneTwoCentralizer G)).inv.hom (0 : Fin 3) =
          (2 : Fin 3) := by
  simp only [Action.autEquivPermCentralizer_mul_apply,
    Action.autEquivPermCentralizer_apply_symm,
    Action.autEquivPermCentralizer_symm_hom_apply,
    Action.autEquivPermCentralizer_symm_inv_apply]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem threePoint_specialization :
    (Action.autEquivPermCentralizer G (Fin 3)
        (swapZeroOneAut G * swapOneTwoAut G) : Equiv.Perm (Fin 3)) =
      Aut.mulEquivPerm (Action.autEquivCentralizer (Action.ofMulAction G (Fin 3))
        (swapZeroOneAut G * swapOneTwoAut G)).val ∧
      (Action.autEquivPermCentralizer G (Fin 3)
        (swapZeroOneAut G * swapOneTwoAut G) : Equiv.Perm (Fin 3)) =
        ((Action.forget (Type 0) G).mapIso
          (swapZeroOneAut G * swapOneTwoAut G)).toEquiv :=
  ⟨Action.coe_autEquivPermCentralizer G (Fin 3) _,
    Action.autEquivPermCentralizer_eq_toEquiv G (Fin 3) _⟩

private theorem threePoint_hom_agreement :
    ((Subgroup.subtype _).comp
        (Action.autEquivCentralizer (Action.ofMulAction G (Fin 3))).toMonoidHom)
          (swapZeroOneAut G * swapOneTwoAut G) =
      (Action.forget (Type 0) G).mapAut (Action.ofMulAction G (Fin 3))
        (swapZeroOneAut G * swapOneTwoAut G) ∧
      ((Subgroup.subtype _).comp (Action.autEquivPermCentralizer G (Fin 3)).toMonoidHom)
          (swapZeroOneAut G * swapOneTwoAut G) =
        ((Aut.mulEquivPerm (α := Fin 3)).toMonoidHom.comp
          ((Action.forget (Type 0) G).mapAut (Action.ofMulAction G (Fin 3))))
            (swapZeroOneAut G * swapOneTwoAut G) := by
  constructor
  · rw [Action.subtype_comp_autEquivCentralizer]
  · rw [Action.subtype_comp_autEquivPermCentralizer]

private theorem threePoint_unit_inverse :
    Action.autEquivPermCentralizer G (Fin 3) 1 = 1 ∧
      Action.autEquivPermCentralizer G (Fin 3) (swapZeroOneAut G * swapOneTwoAut G)⁻¹ =
        (swapZeroOneCentralizer G * swapOneTwoCentralizer G)⁻¹ ∧
      Action.autEquivCentralizer (Action.ofMulAction G (Fin 3)) 1 = 1 ∧
      Action.autEquivCentralizer (Action.ofMulAction G (Fin 3))
          (swapZeroOneAut G * swapOneTwoAut G)⁻¹ =
        (swapZeroOneIsoCentralizer G * swapOneTwoIsoCentralizer G)⁻¹ := by
  simp only [map_one, map_inv, (threePoint_canonical_product G).1,
    (threePoint_canonical_product G).2, and_self]

private theorem threePoint_representation_agreement (g : G) :
    Aut.mulEquivPerm (α := Fin 3) ((Action.ofMulAction G (Fin 3)).ρAut g) =
      (1 : Equiv.Perm (Fin 3)) := by
  rw [Action.mulEquivPerm_ρAut, threePoint_action_perm]

end ThreePoints

section EmptyAction

variable (G : Type u) [Group G]

private abbrev emptyTrivialAction : MulAction G Empty :=
  MulAction.ofEndHom (1 : G →* Function.End Empty)

attribute [local instance] emptyTrivialAction

private def emptyAut : Aut (Action.ofMulAction G Empty) :=
  Action.mkIso (Equiv.refl Empty).toIso fun _ => by
    ext x
    exact Empty.elim x

private def emptyCentralizer :
    Subgroup.centralizer (Set.range (MulAction.toPermHom G Empty)) :=
  ⟨1, Subgroup.one_mem _⟩

private def emptyIsoCentralizer :
    Subgroup.centralizer (Set.range (Action.ofMulAction G Empty).ρAut) :=
  ⟨1, Subgroup.one_mem _⟩

private theorem emptyAut_unique (a : Aut (Action.ofMulAction G Empty)) : a = emptyAut G := by
  apply Aut.ext
  apply Action.hom_ext
  ext x
  exact Empty.elim x

private theorem emptyCentralizer_unique
    (f : Subgroup.centralizer (Set.range (MulAction.toPermHom G Empty))) :
    f = emptyCentralizer G :=
  Subsingleton.elim _ _

private theorem emptyIsoCentralizer_unique
    (f : Subgroup.centralizer (Set.range (Action.ofMulAction G Empty).ρAut)) :
    f = emptyIsoCentralizer G := by
  apply Subtype.ext
  apply Aut.ext
  ext x
  exact Empty.elim x

private theorem empty_underlying_agreement :
    (Action.forget (Type 0) G).mapIso (emptyAut G) =
        (emptyIsoCentralizer G).val ∧
      Aut.mulEquivPerm (α := Empty) ((Action.forget (Type 0) G).mapIso (emptyAut G)) =
        (emptyCentralizer G : Equiv.Perm Empty) := by
  constructor
  · apply Aut.ext
    ext x
    exact Empty.elim x
  · exact Subsingleton.elim _ _

private theorem empty_canonical_forward :
    Action.autEquivCentralizer (Action.ofMulAction G Empty) (emptyAut G) =
        emptyIsoCentralizer G ∧
      Action.autEquivPermCentralizer G Empty (emptyAut G) = emptyCentralizer G := by
  constructor
  · exact emptyIsoCentralizer_unique G _
  · exact emptyCentralizer_unique G _

private theorem empty_canonical_inverse :
    (Action.autEquivCentralizer (Action.ofMulAction G Empty)).symm
        (emptyIsoCentralizer G) = emptyAut G ∧
      (Action.autEquivPermCentralizer G Empty).symm (emptyCentralizer G) = emptyAut G :=
  ⟨emptyAut_unique G _, emptyAut_unique G _⟩

end EmptyAction
