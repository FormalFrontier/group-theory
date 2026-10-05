/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.OpenQuotient
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order

/-!
# A non-injective open quotient of finite spaces

The first projection from a discrete four-point space onto a discrete
two-point space is an open quotient but not an embedding. The generic open
quotient theorem identifies its codomain's connected components.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.OpenQuotient

theorem fst_not_injective :
    ¬ Function.Injective (Prod.fst : Fin 2 × Fin 2 → Fin 2) := by
  intro hinjective
  have heq : ((0 : Fin 2), (0 : Fin 2)) = ((0 : Fin 2), (1 : Fin 2)) :=
    hinjective rfl
  exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd heq)

theorem fst_connectedComponent_zero : connectedComponent (0 : Fin 2) = {0} := by
  exact (totallyDisconnectedSpace_iff_connectedComponent_singleton.mp
    (Topology.IsOpenQuotientMap.totallyDisconnectedSpace
      (isOpenQuotientMap_fst (X := Fin 2) (Y := Fin 2)))) 0

end GroupTheoryTest.Topology.OpenQuotient
