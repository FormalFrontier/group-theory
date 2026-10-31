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

variable [TopologicalSpace (Equiv.Perm (Fin 3))]
  [DiscreteTopology (Equiv.Perm (Fin 3))]

example :
    let g := Equiv.swap (0 : Fin 3) 1
    let z : orbit (Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 3)) :=
      ⟨g • 1, ⟨g, rfl⟩⟩
    let hx : Continuous (fun s : Equiv.Perm (Fin 3) =>
      s • (1 : Equiv.Perm (Fin 3))) := continuous_of_discreteTopology
    let hy : Continuous (fun s : Equiv.Perm (Fin 3) =>
      s • permutationEvalZero 1) :=
      permutationEvalZero.continuous_smul_map 1 hx
    (orbitHomeomorphQuotientStabilizer (Equiv.Perm (Fin 3))
        (permutationEvalZero 1) hy (permutationEvalZero.orbitMap 1 z),
      ((orbitHomeomorphQuotientStabilizer (Equiv.Perm (Fin 3))
        (permutationEvalZero 1) hy).symm (QuotientGroup.mk g) : Fin 3)) =
      (QuotientGroup.mk g, 1) := by
  dsimp only
  let g := Equiv.swap (0 : Fin 3) 1
  let z : orbit (Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 3)) :=
    ⟨g • 1, ⟨g, rfl⟩⟩
  let hx : Continuous (fun s : Equiv.Perm (Fin 3) =>
    s • (1 : Equiv.Perm (Fin 3))) := continuous_of_discreteTopology
  let hy : Continuous (fun s : Equiv.Perm (Fin 3) =>
    s • permutationEvalZero 1) :=
    permutationEvalZero.continuous_smul_map 1 hx
  let e := orbitHomeomorphQuotientStabilizer (Equiv.Perm (Fin 3))
    (permutationEvalZero 1) hy
  change (e.toEquiv (permutationEvalZero.orbitMap 1 z),
      (e.toEquiv.symm (QuotientGroup.mk g) : Fin 3)) =
    (QuotientGroup.mk g, 1)
  have hforward : e.toEquiv (permutationEvalZero.orbitMap 1 z) =
      QuotientGroup.mk g := by
    calc
      _ = MulActionHom.quotientMapOfLE (permutationEvalZero.stabilizer_le 1)
            (orbitHomeomorphQuotientStabilizer (Equiv.Perm (Fin 3))
              (1 : Equiv.Perm (Fin 3)) hx z) :=
        permutationEvalZero.orbitHomeomorphQuotientStabilizer_naturality 1 hx z
      _ = _ := by
        dsimp only [z]
        rw [orbitHomeomorphQuotientStabilizer_apply_smul,
          MulActionHom.quotientMapOfLE_apply_mk]
  apply Prod.ext
  · exact hforward
  · calc
      _ = (permutationEvalZero.orbitMap 1 z : Fin 3) := by
        rw [← hforward, Equiv.symm_apply_apply]
      _ = 1 := by
        rw [MulActionHom.orbitMap_coe]
        change (Equiv.swap (0 : Fin 3) 1) 0 = 1
        exact Equiv.swap_apply_left _ _

end PermutationOrbits
