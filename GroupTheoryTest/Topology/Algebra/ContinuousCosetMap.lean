/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Quotient
public import Mathlib.Analysis.Complex.Circle

/-!
# Circle-valued equivariant maps on the trivial-subgroup quotient

For the regular action of the circle on itself and `H = ⊥`, every `x : Circle`
determines a continuous equivariant map `[g] ↦ g • x`. The parameters `1` and `-1`
give distinct maps. These maps are constructed with the algebraic coset-map
equivalence; their continuity is proved directly by quotient descent from the
continuous orbit map, independently of the coset-map homeomorphism.

The final comparison uses the homeomorphism to recover the same map at `-1`.

## References

Mathlib's circle and its topological group structure, formalized by Heather
Macbeth, and its quotient-map continuity criterion are used without changing
any scalar action or topology.
-/

@[expose] public section

noncomputable section

namespace Circle

/-- The equivariant circle map on cosets associated to a parameter. -/
def cosetAlgebraicMap (x : Circle) :
    (Circle ⧸ (⊥ : Subgroup Circle)) →[Circle] Circle :=
  (MulActionHom.quotientEquivFixedPoints Circle ⊥ Circle).symm ⟨x, bot_le⟩

/-- The coset map for a fixed circle parameter is continuous. -/
theorem cosetAlgebraicMap_continuous (x : Circle) :
    Continuous (cosetAlgebraicMap x) := by
  apply (QuotientGroup.isQuotientMap_mk (⊥ : Subgroup Circle)).continuous_iff.mpr
  have hcomp :
      (cosetAlgebraicMap x : Circle ⧸ (⊥ : Subgroup Circle) → Circle) ∘
          (QuotientGroup.mk : Circle → Circle ⧸ (⊥ : Subgroup Circle)) =
        fun g : Circle => g • x := by
    funext g
    exact MulActionHom.quotientEquivFixedPoints_symm_apply_mk ⟨x, bot_le⟩ g
  rw [hcomp]
  exact continuous_id.smul continuous_const

/-- The circle's regular orbit map on the quotient by the trivial subgroup. -/
def continuousCosetMap (x : Circle) :
    ContinuousMulActionHom (@_root_.id Circle) (Circle ⧸ (⊥ : Subgroup Circle)) Circle :=
  ContinuousMulActionHom.ofMulActionHom (cosetAlgebraicMap x)
    (cosetAlgebraicMap_continuous x)

/-- A representative is sent to its product with the parameter. -/
@[simp]
theorem continuousCosetMap_apply_mk (x g : Circle) :
    continuousCosetMap x (QuotientGroup.mk g) = g • x :=
  MulActionHom.quotientEquivFixedPoints_symm_apply_mk ⟨x, bot_le⟩ g

/-- The parameters `1` and `-1` give different continuous equivariant maps. -/
theorem continuousCosetMap_one_ne_neg_one :
    continuousCosetMap 1 ≠ continuousCosetMap (-1) := by
  intro h
  have heval := congrArg
    (fun f : ContinuousMulActionHom (@_root_.id Circle)
      (Circle ⧸ (⊥ : Subgroup Circle)) Circle => f (QuotientGroup.mk (1 : Circle))) h
  have hx : (1 : Circle) = -1 := by
    simpa only [continuousCosetMap_apply_mk, one_smul] using heval
  exact (Circle.neg_ne_self 1) hx.symm

/-- Every point of the regular circle action is fixed by the trivial subgroup. -/
def trivialSubgroupFixedPoint (x : Circle) :
    ↥(MulAction.fixedPoints (⊥ : Subgroup Circle) Circle) :=
  ⟨x, MulAction.mem_fixedPoints_subgroup_iff.mpr bot_le⟩

/-- The inverse coset-map homeomorphism at `-1` recovers the separately constructed
continuous circle map. -/
theorem quotientHomeomorphFixedPoints_symm_neg_one :
    (ContinuousMulActionHom.quotientHomeomorphFixedPoints Circle ⊥ Circle).symm
        (trivialSubgroupFixedPoint (-1)) = continuousCosetMap (-1) := by
  apply ContinuousMulActionHom.toMulActionHom_injective
  exact ContinuousMulActionHom.quotientHomeomorphFixedPoints_symm_toMulActionHom
    (trivialSubgroupFixedPoint (-1))

end Circle
