/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Product coset orbits and double cosets

For subgroups `H` and `K` of a group `G`, the componentwise left action of `G` on
`(G ⧸ H) × (G ⧸ K)` has orbit quotient equivalent to the double-coset quotient `H \ G / K`.
The correspondence sends the orbit of `(xH, yK)` to `H (x⁻¹ * y) K`. Its inverse sends
`H g K` to the orbit of `(H, gK)`. These formulas specify classes, not unique representatives.
Neither subgroup needs to be normal.

## Main declarations

* `MulAction.orbitQuotientProdQuotientEquivDoubleCoset`: the equivalence of quotients.
* `MulAction.orbitQuotientProdQuotientEquivDoubleCoset_apply_mk`: its forward projection formula.
* `MulAction.orbitQuotientProdQuotientEquivDoubleCoset_symm_apply_mk`:
  its inverse projection formula.
* `MulAction.orbitRel_prod_quotient_mk_eq_mk_iff`: equality of pair orbits in double-coset terms.

## Implementation notes

The construction descends `(x, y) ↦ H (x⁻¹ * y) K` through the two coset quotients and then
the orbit quotient. The inverse descends `g ↦ orbit(H, gK)` through the double-coset quotient.
The normalization is simultaneous left multiplication by `x⁻¹`. Extensionality uses `Equiv.ext`
and quotient induction; functions to an independent `Type v` use `Setoid.liftEquiv` and
`Setoid.lift_unique`.

## References

The quotient constructions and actions are those of
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5):
`GroupTheory/DoubleCoset.lean` by Chris Birkbeck; `GroupTheory/Coset/Defs.lean` by Mitchell Rowett
and Kim Morrison; `GroupTheory/GroupAction/Defs.lean` by Chris Hughes;
`GroupTheory/GroupAction/Quotient.lean` by Chris Hughes and Thomas Browning; and
`Algebra/Group/Action/Prod.lean` by Simon Hudon, Patrick Massot and Eric Wieser.
-/

@[expose] public section

universe u

namespace MulAction

variable {G : Type u} [Group G]

/-- Diagonal left orbits of pairs of left cosets correspond to double cosets.
The forward map sends the orbit of `(xH, yK)` to `H (x⁻¹ * y) K`, and the inverse sends
`H g K` to the orbit of `(H, gK)`. -/
def orbitQuotientProdQuotientEquivDoubleCoset (H K : Subgroup G) :
    orbitRel.Quotient G ((G ⧸ H) × (G ⧸ K)) ≃
      DoubleCoset.Quotient (H : Set G) (K : Set G) := by
  let f (p : (G ⧸ H) × (G ⧸ K)) : DoubleCoset.Quotient (H : Set G) (K : Set G) :=
    _root_.Quotient.liftOn₂
      (s₁ := QuotientGroup.leftRel H) (s₂ := QuotientGroup.leftRel K)
      p.1 p.2 (fun x y : G => DoubleCoset.mk H K (x⁻¹ * y))
      (fun (x₁ y₁ x₂ y₂ : G)
        (hH : QuotientGroup.leftRel H x₁ x₂)
        (hK : QuotientGroup.leftRel K y₁ y₂) => by
        apply DoubleCoset.eq.mpr
        refine ⟨(x₁⁻¹ * x₂)⁻¹, H.inv_mem (QuotientGroup.leftRel_apply.mp hH),
          y₁⁻¹ * y₂, QuotientGroup.leftRel_apply.mp hK, ?_⟩
        simp [mul_assoc])
  have f_mk (x y : G) :
      f (QuotientGroup.mk (s := H) x, QuotientGroup.mk (s := K) y) =
        DoubleCoset.mk H K (x⁻¹ * y) := rfl
  exact {
    toFun :=
      _root_.Quotient.lift
        (s := orbitRel G ((G ⧸ H) × (G ⧸ K)))
        f
        (fun p q hpq => by
          change ∃ a : G, a • q = p at hpq
          rcases hpq with ⟨a, rfl⟩
          rcases q with ⟨qH, qK⟩
          refine QuotientGroup.induction_on qH ?_
          intro x
          refine QuotientGroup.induction_on qK ?_
          intro y
          simp only [Prod.smul_mk, Quotient.smul_mk, smul_eq_mul, f_mk]
          rw [mul_inv_rev, mul_assoc]
          simp)
    invFun :=
      _root_.Quotient.lift
        (s := DoubleCoset.setoid (H : Set G) (K : Set G))
        (fun g : G =>
          _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
            (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) g))
        (fun g g' hgg' => by
          rcases DoubleCoset.rel_iff.mp hgg' with ⟨h, hh, k, hk, rfl⟩
          symm
          apply _root_.Quotient.sound
          change ∃ a : G,
            a • (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) g) =
              (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) (h * g * k))
          refine ⟨h, ?_⟩
          apply Prod.ext
          · simpa only [Prod.smul_fst, Quotient.smul_mk, smul_eq_mul, mul_one, one_mul]
              using (QuotientGroup.mk_mul_of_mem (s := H) (1 : G) hh)
          · simpa only [Prod.smul_snd, Quotient.smul_mk, smul_eq_mul]
              using (QuotientGroup.mk_mul_of_mem (s := K) (h * g) hk).symm)
    left_inv := by
      intro q
      refine _root_.Quotient.inductionOn q ?_
      rintro ⟨qH, qK⟩
      refine QuotientGroup.induction_on qH ?_
      intro x
      refine QuotientGroup.induction_on qK ?_
      intro y
      change _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
          (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) (x⁻¹ * y)) =
        _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
          (QuotientGroup.mk (s := H) x, QuotientGroup.mk (s := K) y)
      apply _root_.Quotient.sound
      change ∃ a : G,
        a • (QuotientGroup.mk (s := H) x, QuotientGroup.mk (s := K) y) =
          (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) (x⁻¹ * y))
      refine ⟨x⁻¹, ?_⟩
      apply Prod.ext <;> simp [Quotient.smul_mk, smul_eq_mul]
    right_inv := by
      intro d
      refine _root_.Quotient.inductionOn d ?_
      intro g
      change DoubleCoset.mk H K ((1 : G)⁻¹ * g) = DoubleCoset.mk H K g
      simp }

/-- The forward projection formula for the product-coset orbit equivalence. -/
@[simp]
theorem orbitQuotientProdQuotientEquivDoubleCoset_apply_mk (H K : Subgroup G) (x y : G) :
    orbitQuotientProdQuotientEquivDoubleCoset H K
        (_root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
          (QuotientGroup.mk (s := H) x, QuotientGroup.mk (s := K) y)) =
      DoubleCoset.mk H K (x⁻¹ * y) := by
  rfl

/-- The inverse projection formula for the product-coset orbit equivalence. -/
@[simp]
theorem orbitQuotientProdQuotientEquivDoubleCoset_symm_apply_mk (H K : Subgroup G) (g : G) :
    (orbitQuotientProdQuotientEquivDoubleCoset H K).symm (DoubleCoset.mk H K g) =
      _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
        (QuotientGroup.mk (s := H) (1 : G), QuotientGroup.mk (s := K) g) := by
  rfl

/-- Two pairs of left cosets lie in the same diagonal orbit exactly when their relative
products lie in the same double coset. -/
theorem orbitRel_prod_quotient_mk_eq_mk_iff (H K : Subgroup G) (x y x' y' : G) :
    _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
        (QuotientGroup.mk (s := H) x, QuotientGroup.mk (s := K) y) =
      _root_.Quotient.mk (orbitRel G ((G ⧸ H) × (G ⧸ K)))
        (QuotientGroup.mk (s := H) x', QuotientGroup.mk (s := K) y') ↔
      ∃ h ∈ H, ∃ k ∈ K, x'⁻¹ * y' = h * (x⁻¹ * y) * k := by
  constructor
  · intro hp
    apply DoubleCoset.eq.mp
    simpa only [orbitQuotientProdQuotientEquivDoubleCoset_apply_mk]
      using congrArg (orbitQuotientProdQuotientEquivDoubleCoset H K) hp
  · intro hd
    apply (orbitQuotientProdQuotientEquivDoubleCoset H K).injective
    rw [orbitQuotientProdQuotientEquivDoubleCoset_apply_mk,
      orbitQuotientProdQuotientEquivDoubleCoset_apply_mk]
    exact DoubleCoset.eq.mpr hd

end MulAction
