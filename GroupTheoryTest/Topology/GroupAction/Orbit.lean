/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.GroupAction.Orbit
import GroupTheory.Topology.GroupAction.Orbit
import Mathlib.Algebra.Group.Action.End
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

/-!
# Regular integer orbits

The regular action of `Multiplicative Int` has an infinite, noncompact discrete orbit.
Translation of `ofAdd 1` by `ofAdd 1` is evaluated through the homeomorphism API.
-/

open MulAction Multiplicative

example :
    ((orbitHomeomorphQuotientStabilizer (Multiplicative Int)
      (ofAdd (1 : Int)) continuous_of_discreteTopology).symm
      (QuotientGroup.mk (ofAdd 1)) : Multiplicative Int) = ofAdd 2 := by
  calc
    _ = (ofAdd 1 : Multiplicative Int) • ofAdd 1 :=
      orbitHomeomorphQuotientStabilizer_symm_mk_coe
        (Multiplicative Int) (ofAdd (1 : Int))
        continuous_of_discreteTopology (ofAdd 1)
    _ = ofAdd 2 := rfl

/-!
# Evaluation of regular permutation orbits

Evaluation at zero maps the regular left action of permutations to the standard
action on `Fin 3`. The algebraic orbit-stabilizer equivalence and its inverse
evaluate the transposition `(0 1)` on this six-to-three orbit map.
-/

open MulAction

section PermutationOrbits

private def permutationEvalZero :
    Equiv.Perm (Fin 3) →[Equiv.Perm (Fin 3)] Fin 3 where
  toFun s := s 0
  map_smul' _ _ := rfl

example :
    let g := Equiv.swap (0 : Fin 3) 1
    let z : orbit (Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 3)) :=
      ⟨g • 1, ⟨g, rfl⟩⟩
    (orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3))
        (permutationEvalZero 1) (permutationEvalZero.orbitMap 1 z),
      ((orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3))
        (permutationEvalZero 1)).symm (QuotientGroup.mk g) : Fin 3)) =
      (QuotientGroup.mk g, 1) := by
  dsimp only
  have hforward :
      orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3)) (permutationEvalZero 1)
        (permutationEvalZero.orbitMap 1
          ⟨Equiv.swap (0 : Fin 3) 1 • 1, ⟨Equiv.swap 0 1, rfl⟩⟩) =
        QuotientGroup.mk (Equiv.swap (0 : Fin 3) 1) := by
    have hregular :
        orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3))
            (1 : Equiv.Perm (Fin 3))
            ⟨Equiv.swap (0 : Fin 3) 1 • 1, ⟨Equiv.swap 0 1, rfl⟩⟩ =
          QuotientGroup.mk (Equiv.swap (0 : Fin 3) 1) := by
      apply (orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3))
        (1 : Equiv.Perm (Fin 3))).symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply,
        orbitEquivQuotientStabilizer_symm_apply]
    calc
      _ = MulActionHom.quotientMapOfLE (permutationEvalZero.stabilizer_le 1)
            (orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3)) 1
              ⟨Equiv.swap (0 : Fin 3) 1 • 1, ⟨Equiv.swap 0 1, rfl⟩⟩) :=
        permutationEvalZero.orbitEquivQuotientStabilizer_naturality 1 _
      _ = _ := by rw [hregular, MulActionHom.quotientMapOfLE_apply_mk]
  apply Prod.ext
  · exact hforward
  · calc
      _ = (permutationEvalZero.orbitMap 1
          ⟨Equiv.swap (0 : Fin 3) 1 • 1, ⟨Equiv.swap 0 1, rfl⟩⟩ : Fin 3) := by
        simpa only [Equiv.symm_apply_apply] using
          congrArg (fun q => ((orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3))
            (permutationEvalZero 1)).symm q : Fin 3)) hforward.symm
      _ = 1 := by
        rw [MulActionHom.orbitMap_coe]
        change (Equiv.swap (0 : Fin 3) 1) 0 = 1
        exact Equiv.swap_apply_left _ _

end PermutationOrbits
