/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant maps from coset actions

For a subgroup `H` of a group `G`, a `G`-equivariant map from the left cosets `G ⧸ H`
to a `G`-set `X` is determined by the image of the identity coset. This image can be any
point fixed by `H`, expressed as the condition `H ≤ MulAction.stabilizer G x`.

`MulActionHom.quotientEquivFixedPoints` realizes this universal property. Its inverse
sends the coset of `g` to `g • x`. No normality of `H` or transitivity of `X` is needed.
The fixed-point subtype need not be stable under `G`, so the result is a plain equivalence.

For another subgroup `K`, `MulActionHom.nonempty_quotient_iff_exists_le_map_conj`
characterizes existence of an equivariant map `G ⧸ H → G ⧸ K` by containment
`H ≤ gKg⁻¹` for some `g : G`. The associated map sends the coset of `x` to the
coset of `x * g`; neither subgroup needs to be normal.

## Implementation notes

The inverse uses Mathlib's `MulAction.ofQuotientStabilizer` after
`Subgroup.quotientMapOfLE`. The fixed-point condition is related to
`MulAction.fixedPoints` by `MulAction.mem_fixedPoints_subgroup_iff`.

## References

The construction uses the coset maps and orbit–stabilizer maps in Mathlib's
`Mathlib.GroupTheory.Coset.Basic` and `Mathlib.GroupTheory.GroupAction.Quotient`,
and the equivariant-map API in `Mathlib.GroupTheory.GroupAction.Hom`.
The existence criterion combines this universal property with Mathlib's stabilizer
formula for a translated point in `Mathlib.GroupTheory.GroupAction.Basic`.
-/

@[expose] public section

universe u v w

namespace MulAction

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- A point is fixed by a subgroup exactly when that subgroup lies in its stabilizer. -/
theorem mem_fixedPoints_subgroup_iff {H : Subgroup G} {x : X} :
    x ∈ fixedPoints H X ↔ H ≤ stabilizer G x := by
  constructor
  · intro hx g hg
    exact hx ⟨g, hg⟩
  · intro hx g
    exact hx g.property

end MulAction

namespace MulActionHom

/-- Equivariant maps from the left cosets `G ⧸ H` to `X` correspond to points of `X`
fixed by `H`. The forward map evaluates at the identity coset, and the inverse sends
`QuotientGroup.mk g` to `g • x`. -/
def quotientEquivFixedPoints (G : Type u) [Group G] (H : Subgroup G)
    (X : Type v) [MulAction G X] :
    ((G ⧸ H) →[G] X) ≃ {x : X // H ≤ MulAction.stabilizer G x} where
  toFun f := ⟨f (QuotientGroup.mk (1 : G)), by
    intro g hg
    have hg' : g ∈ MulAction.stabilizer G
        (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rwa [MulAction.stabilizer_quotient H]
    change g • f (QuotientGroup.mk (1 : G)) = f (QuotientGroup.mk (1 : G))
    rw [← f.map_smul]
    exact congrArg f (MulAction.mem_stabilizer_iff.mp hg')⟩
  invFun x :=
    { toFun := MulAction.ofQuotientStabilizer G x.val ∘
        Subgroup.quotientMapOfLE x.property
      map_smul' := by
        intro g q
        change MulAction.ofQuotientStabilizer G x.val
            (Subgroup.quotientMapOfLE x.property (g • q)) =
          g • MulAction.ofQuotientStabilizer G x.val
            (Subgroup.quotientMapOfLE x.property q)
        refine Quotient.inductionOn' q ?_
        intro a
        simpa only [MulAction.Quotient.smul_mk, Subgroup.quotientMapOfLE_apply_mk] using
          MulAction.ofQuotientStabilizer_smul G x.val g (QuotientGroup.mk a) }
  left_inv f := by
    apply MulActionHom.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    change g • f (QuotientGroup.mk (1 : G)) = f (QuotientGroup.mk g)
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] using
      (f.map_smul g (QuotientGroup.mk (1 : G))).symm
  right_inv x := by
    apply Subtype.ext
    change MulAction.ofQuotientStabilizer G x.val
      (Subgroup.quotientMapOfLE x.property (QuotientGroup.mk (1 : G))) = x.val
    rw [Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk, one_smul]

variable {G : Type u} [Group G] {H : Subgroup G}
variable {X : Type v} [MulAction G X]

/-- The universal-property equivalence evaluates a map at the identity coset. -/
@[simp]
theorem quotientEquivFixedPoints_apply (f : (G ⧸ H) →[G] X) :
    (quotientEquivFixedPoints G H X f).val = f (QuotientGroup.mk (1 : G)) :=
  rfl

/-- The map corresponding to an `H`-fixed point sends the coset of `g` to `g • x`. -/
@[simp]
theorem quotientEquivFixedPoints_symm_apply_mk
    (x : {x : X // H ≤ MulAction.stabilizer G x}) (g : G) :
    (quotientEquivFixedPoints G H X).symm x (QuotientGroup.mk g) = g • x.val := by
  change MulAction.ofQuotientStabilizer G x.val
    (Subgroup.quotientMapOfLE x.property (QuotientGroup.mk g)) = g • x.val
  rw [Subgroup.quotientMapOfLE_apply_mk, MulAction.ofQuotientStabilizer_mk]

/-- Two equivariant maps from left cosets agree if they agree at the identity coset. -/
theorem quotient_ext {f g : (G ⧸ H) →[G] X}
    (h : f (QuotientGroup.mk (1 : G)) = g (QuotientGroup.mk (1 : G))) : f = g := by
  apply (quotientEquivFixedPoints G H X).injective
  exact Subtype.ext h

/-- Equality of equivariant maps from left cosets is equality at the identity coset. -/
theorem quotient_ext_iff {f g : (G ⧸ H) →[G] X} :
    f = g ↔ f (QuotientGroup.mk (1 : G)) = g (QuotientGroup.mk (1 : G)) :=
  ⟨fun h ↦ congrArg (fun k : (G ⧸ H) →[G] X ↦ k (QuotientGroup.mk (1 : G))) h,
    quotient_ext⟩

/-- The inverse equivalence gives the unique equivariant map with the prescribed value
at the identity coset. -/
theorem quotientEquivFixedPoints_symm_eq_iff
    (x : {x : X // H ≤ MulAction.stabilizer G x}) (f : (G ⧸ H) →[G] X) :
    (quotientEquivFixedPoints G H X).symm x = f ↔
      f (QuotientGroup.mk (1 : G)) = x.val := by
  rw [quotient_ext_iff, quotientEquivFixedPoints_symm_apply_mk, one_smul]
  exact eq_comm

/-- Evaluation at the identity coset is natural under postcomposition by an equivariant
map, as an equality in the whole fixed-point subtype. -/
theorem quotientEquivFixedPoints_comp {Y : Type w} [MulAction G Y]
    (k : X →[G] Y) (f : (G ⧸ H) →[G] X) :
    quotientEquivFixedPoints G H Y (k.comp f) =
      ⟨k (quotientEquivFixedPoints G H X f).val, by
        intro g hg
        change g • k (quotientEquivFixedPoints G H X f).val =
          k (quotientEquivFixedPoints G H X f).val
        rw [← k.map_smul]
        exact congrArg k ((quotientEquivFixedPoints G H X f).property hg)⟩ := by
  apply Subtype.ext
  rfl

/-- At the stabilizer of `x`, the inverse equivalence agrees with Mathlib's canonical
unbundled map from the quotient by the stabilizer, without a transitivity assumption. -/
theorem quotientEquivFixedPoints_symm_stabilizer (x : X) :
    (((quotientEquivFixedPoints G (MulAction.stabilizer G x) X).symm ⟨x, le_rfl⟩) :
      (G ⧸ MulAction.stabilizer G x) → X) = MulAction.ofQuotientStabilizer G x := by
  funext q
  refine Quotient.inductionOn' q ?_
  intro g
  rw [quotientEquivFixedPoints_symm_apply_mk, MulAction.ofQuotientStabilizer_mk]

/-- An equivariant map between left-coset actions exists exactly when `H` is contained
in a conjugate `gKg⁻¹` of `K`. The fixed-point universal property at the coset of `g`
gives the map `[x] ↦ [x * g]`; its well-definedness is `g⁻¹ * h * g ∈ K` for `h ∈ H`.
No normality or finiteness hypothesis is required. -/
theorem nonempty_quotient_iff_exists_le_map_conj (H K : Subgroup G) :
    Nonempty ((G ⧸ H) →[G] (G ⧸ K)) ↔
      ∃ g : G, H ≤ K.map (MulAut.conj g).toMonoidHom := by
  rw [(quotientEquivFixedPoints G H (G ⧸ K)).nonempty_congr,
    nonempty_subtype, QuotientGroup.exists_mk]
  apply exists_congr
  intro g
  have hg : MulAction.stabilizer G (QuotientGroup.mk g : G ⧸ K) =
      K.map (MulAut.conj g).toMonoidHom := by
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      MulAction.stabilizer_quotient] using
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g
        (QuotientGroup.mk (1 : G) : G ⧸ K)
  rw [hg]

end MulActionHom
