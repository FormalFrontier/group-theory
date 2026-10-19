/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Option
public import Mathlib.Algebra.Module.PUnit

/-!
# Equivariant maps from permutation cosets

For the permutation action on `Option (Fin 3)`, the orbit map at `some 0` and
constant-`none` map have distinct identity-coset values. The coset universal
property recovers each whole equivariant map from its value. Empty targets and
the trivial-group action on one point give boundary cases.

The permutation action has two orbits and is not free; the stabilizer of
`some 0` is not normal. These descriptions are mathematical context, not
additional assertions proved here.

## References and credit

* Mathlib's coset and permutation action constructions (Chris Hughes, Thomas
  Browning and Yury Kudryashov), equivariant-map structures (Kenny Lau and Antoine
  Chambert-Loir), and option actions (Yaël Dillies) supply the constructions.
* Mathlib's one-point action instances (Kenny Lau) supply the boundary actions.
-/

set_option linter.privateModule false

@[expose] public section

namespace MulActionHom

/-- The orbit map at `some 0` and the constant-`none` map from stabilizer cosets
for the permutation action on `Option (Fin 3)`. -/
private def permutationOptionCosetMaps :=
  let G := Equiv.Perm (Fin 3)
  let X := Option (Fin 3)
  let x₀ : X := some (0 : Fin 3)
  let H : Subgroup G := MulAction.stabilizer G x₀
  show ((G ⧸ H) →[G] X) × ((G ⧸ H) →[G] X) from
    ( { toFun := MulAction.ofQuotientStabilizer G x₀
        map_smul' := MulAction.ofQuotientStabilizer_smul G x₀ },
      { toFun := fun _ => (none : X)
        map_smul' := fun g _ => (Option.smul_none (α := Fin 3) g).symm } )

/-- Evaluation at `QuotientGroup.mk (1 : G)` gives `some 0`, and the inverse
universal property reconstructs the whole orbit map. -/
private theorem permutationOption_orbit_map :
    let G := Equiv.Perm (Fin 3)
    let X := Option (Fin 3)
    let H := MulAction.stabilizer G (some (0 : Fin 3) : X)
    let e := quotientEquivFixedPoints G H X
    (e permutationOptionCosetMaps.1).val = some (0 : Fin 3) ∧
      e.symm (e permutationOptionCosetMaps.1) = permutationOptionCosetMaps.1 := by
  dsimp only
  exact ⟨rfl, Equiv.symm_apply_apply _ _⟩

/-- The same equivalence evaluates the constant map to `none` and reconstructs
that whole map, although its value has a larger stabilizer. -/
private theorem permutationOption_constant_map :
    let G := Equiv.Perm (Fin 3)
    let X := Option (Fin 3)
    let H := MulAction.stabilizer G (some (0 : Fin 3) : X)
    let e := quotientEquivFixedPoints G H X
    (e permutationOptionCosetMaps.2).val = (none : X) ∧
      e.symm (e permutationOptionCosetMaps.2) = permutationOptionCosetMaps.2 := by
  dsimp only
  exact ⟨rfl, Equiv.symm_apply_apply _ _⟩

-- An empty target gives no equivariant map, without a nonempty-target assumption.
example : IsEmpty
    (@MulActionHom Unit Unit (@id Unit) (Unit ⧸ (⊤ : Subgroup Unit))
      (MulAction.quotient Unit (⊤ : Subgroup Unit)).toSMul
      Empty (inferInstance : MulAction Unit Empty).toSMul) :=
  ⟨fun f => (quotientEquivFixedPoints Unit (⊤ : Subgroup Unit) Empty f).val.elim⟩

-- With trivial group and one-point target, the inverse gives the unique map.
example :
    ∃! f : @MulActionHom Unit Unit (@id Unit) (Unit ⧸ (⊤ : Subgroup Unit))
      (MulAction.quotient Unit (⊤ : Subgroup Unit)).toSMul
      Unit (inferInstance : MulAction Unit Unit).toSMul, True := by
  let e := quotientEquivFixedPoints Unit (⊤ : Subgroup Unit) Unit
  refine ⟨e.symm ⟨(), ?_⟩, trivial, ?_⟩
  · intro g _
    exact Subsingleton.elim _ _
  · intro f _
    apply e.injective
    exact Subsingleton.elim _ _

end MulActionHom
