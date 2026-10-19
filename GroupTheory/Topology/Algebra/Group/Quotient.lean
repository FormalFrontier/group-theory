/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
public import GroupTheory.Topology.Algebra.ConstMulAction
public import GroupTheory.GroupAction.Quotient
public import GroupTheory.Topology.Algebra.MulActionHom

/-!
# Subgroups and the topology of left-coset quotients

For an arbitrary subgroup `H`, openness is equivalent to discreteness of the
canonical left-coset quotient `G ⧸ H`, and closedness is equivalent to its T1
separation property, when fixed left translations are continuous. An open
subgroup is clopen without an index assumption. At finite index, openness,
closedness and clopenness are equivalent. Compactness is needed only to deduce
finite index from openness. Neither normality, right-translation continuity,
joint multiplication, continuous inversion nor ambient separation is assumed.
Fixed left actions on the canonical quotient inherit continuity from the source,
for every subgroup; the additive quotient has the corresponding fixed-addition
instance.

Continuous equivariant maps on `G ⧸ H` carry the compact-open subspace topology.
`ContinuousMulActionHom.quotientHomeomorphFixedPoints` identifies this space with
`MulAction.fixedPoints H X` in its usual subspace topology. For this construction,
right translations of `G` must be continuous and the action on `X` must be jointly
continuous. No continuity of varying inversion is needed.

## Implementation notes

The quotient and its coinduced topology are Mathlib's existing objects. A singleton
fiber over the class of `g` is the left coset `g • H`; `IsOpen.smul`, `IsClosed.smul`
and the coinducing projection relate subgroup properties to quotient singletons.
A finite T1 space is discrete. These facts do not require the stronger
arbitrary-subgroup open-projection theorem, whose right-saturation argument
requires right translations. The continuous coset-map construction uses the
existing algebraic equivalence `MulActionHom.quotientEquivFixedPoints` and
`MulAction.mem_fixedPoints_subgroup_iff`. Its inverse family descends the joint
action along the identity times the open quotient projection, then uses the
one-way compact-open currying theorem, not a joint-evaluation converse.

## References

* Mathlib's `QuotientGroup.eq_class_eq_leftCoset`, `QuotientGroup.preimage_mk_one`,
  `QuotientGroup.isQuotientMap_mk`, `IsOpen.smul`, `IsClosed.smul`,
  `Finite.instDiscreteTopology` and compact-discrete finiteness.
* Mathlib's `QuotientGroup.discreteTopology_iff`, `QuotientGroup.t1Space_iff`,
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.isOpen_of_isClosed_of_finiteIndex`
  and `Subgroup.isClosed_of_isOpen` provide separately continuous specializations.
* Mathlib's compact-open topology, fixed-point evaluation and
  `ContinuousMap.continuous_of_continuous_uncurry`, together with products of
  open quotient maps, supply the continuous-family interfaces.
-/

@[expose] public section

open scoped Pointwise

universe u

namespace QuotientGroup

/-- Fixed left multiplication induces continuous fixed actions on the canonical
left-coset quotient by any subgroup. This extends Mathlib's
`QuotientGroup.instContinuousConstSMul` from separately continuous multiplication
without changing the quotient, its action or its topology. -/
@[to_additive
/-- Fixed left addition induces continuous fixed actions on the canonical coset
quotient by any additive subgroup. This extends Mathlib's
`QuotientAddGroup.instContinuousConstVAdd` from separately continuous addition
without changing the quotient, its action or its topology. -/]
instance (priority := 100) continuousConstSMul
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) : ContinuousConstSMul G (G ⧸ H) := by
  exact Topology.IsCoinducing.continuousConstSMul
    { toFun := (QuotientGroup.mk : G → G ⧸ H)
      map_smul' := fun g x => (MulAction.Quotient.smul_mk H g x).symm }
    (QuotientGroup.isQuotientMap_mk H).isCoinducing

/-- The fixed-action continuity instance agrees with Mathlib's separately
continuous provider on the same canonical left-coset quotient. -/
@[to_additive
/-- The fixed-addition continuity instance agrees with Mathlib's separately
continuous provider on the same canonical coset quotient. -/]
theorem continuousConstSMul_eq
    {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (H : Subgroup G) :
    continuousConstSMul H =
      (QuotientGroup.instContinuousConstSMul (N := H) : ContinuousConstSMul G (G ⧸ H)) := by
  exact Subsingleton.elim _ _

end QuotientGroup

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- A subgroup is open exactly when its canonical left-coset quotient is discrete,
assuming only continuity of fixed left translations. Compactness and normality
are not required. The supplied quotient topology is unchanged. -/
@[to_additive]
theorem isOpen_iff_discreteTopology_quotient (H : Subgroup G) :
    IsOpen (H : Set G) ↔ DiscreteTopology (G ⧸ H) := by
  constructor
  · intro hH
    refine discreteTopology_iff_isOpen_singleton.mpr ?_
    refine QuotientGroup.mk_surjective.forall.2 fun g ↦ ?_
    apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isOpen_preimage.mp
    have hfiber : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {QuotientGroup.mk g} =
        g • (H : Set G) := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        QuotientGroup.eq_class_eq_leftCoset H g
    rw [hfiber]
    exact hH.smul g
  · intro hQ
    let : DiscreteTopology (G ⧸ H) := hQ
    rw [← QuotientGroup.preimage_mk_one H]
    exact (isOpen_discrete _).preimage QuotientGroup.continuous_mk

/-- An open subgroup of a compact group equipped with a topology has finite index
if fixed left translations are continuous. No joint multiplication, continuous
inversion, right translations, separation or normality is required. -/
theorem finiteIndex_of_isOpen [CompactSpace G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  let : DiscreteTopology (G ⧸ H) := (H.isOpen_iff_discreteTopology_quotient).mp hH
  let : Finite (G ⧸ H) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- A subgroup is closed exactly when its canonical left-coset quotient is T1,
assuming continuity of fixed left translations. No finite-index, compactness,
normality or ambient separation assumption is needed. This extends Mathlib's
`QuotientGroup.t1Space_iff` from separately continuous multiplication. -/
theorem isClosed_iff_t1Space_quotient (H : Subgroup G) :
    IsClosed (H : Set G) ↔ T1Space (G ⧸ H) := by
  constructor
  · intro hH
    refine ⟨?_⟩
    refine QuotientGroup.mk_surjective.forall.2 fun g ↦ ?_
    apply (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage.mp
    have hfiber : (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {QuotientGroup.mk g} =
        g • (H : Set G) := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        QuotientGroup.eq_class_eq_leftCoset H g
    rw [hfiber]
    exact hH.smul g
  · intro hQ
    let : T1Space (G ⧸ H) := hQ
    rw [← QuotientGroup.preimage_mk_one H]
    exact (isClosed_singleton (x := (QuotientGroup.mk : G → G ⧸ H) 1)).preimage
      QuotientGroup.continuous_mk

/-- A subgroup is clopen exactly when it is open, assuming continuity of fixed
left translations. No finite-index or compactness assumption is needed. The
open-to-closed implication extends Mathlib's `Subgroup.isClosed_of_isOpen` from
separately continuous multiplication. -/
theorem isClopen_iff_isOpen (H : Subgroup G) :
    IsClopen (H : Set G) ↔ IsOpen (H : Set G) := by
  constructor
  · exact fun hH ↦ hH.isOpen
  · intro hH
    let : DiscreteTopology (G ⧸ H) := (H.isOpen_iff_discreteTopology_quotient).mp hH
    exact ⟨(H.isClosed_iff_t1Space_quotient).mpr inferInstance, hH⟩

/-- A finite-index subgroup is open exactly when it is closed, assuming continuity
of fixed left translations. Compactness and normality are not required. The
closed-to-open implication extends Mathlib's
`Subgroup.isOpen_of_isClosed_of_finiteIndex` from separately continuous multiplication. -/
theorem isOpen_iff_isClosed (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H : Set G) ↔ IsClosed (H : Set G) := by
  constructor
  · intro hH
    exact ((H.isClopen_iff_isOpen).mpr hH).isClosed
  · intro hH
    let : T1Space (G ⧸ H) := (H.isClosed_iff_t1Space_quotient).mp hH
    let : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact (H.isOpen_iff_discreteTopology_quotient).mpr Finite.instDiscreteTopology

/-- A finite-index subgroup is clopen exactly when it is closed, assuming continuity
of fixed left translations. Compactness, normality and ambient separation are not
required. This combines the closed-to-open implication of Mathlib's
`Subgroup.isOpen_of_isClosed_of_finiteIndex` with the definition of clopenness. -/
theorem isClopen_iff_isClosed (H : Subgroup G) [H.FiniteIndex] :
    IsClopen (H : Set G) ↔ IsClosed (H : Set G) := by
  exact (H.isClopen_iff_isOpen).trans H.isOpen_iff_isClosed

end Subgroup

namespace QuotientGroup

/-- The left-coset projection is an open quotient map when each right translation
of the group is continuous. The subgroup need not be normal or closed. This
extends `QuotientGroup.isOpenQuotientMap_mk` without requiring left translations. -/
theorem isOpenQuotientMap_mk_of_continuousConstSMul_op
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul Gᵐᵒᵖ G]
    (H : Subgroup G) : IsOpenQuotientMap (mk : G → G ⧸ H) := by
  refine IsOpenQuotientMap.of_isOpenMap_isQuotientMap ?_ (isQuotientMap_mk H)
  intro U hU
  rw [← (isQuotientMap_mk H).isCoinducing.isOpen_preimage, preimage_image_mk_eq_mul]
  exact hU.mul_right

/-- Under separately continuous multiplication, the right-translation formulation
of openness agrees with Mathlib's open quotient map on the same coset space. -/
theorem isOpenQuotientMap_mk_of_continuousConstSMul_op_eq
    {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    (H : Subgroup G) :
    isOpenQuotientMap_mk_of_continuousConstSMul_op H =
      (isOpenQuotientMap_mk (N := H) : IsOpenQuotientMap (mk : G → G ⧸ H)) := by
  exact Subsingleton.elim _ _

end QuotientGroup

universe v

namespace ContinuousMulActionHom

section FixedPointMap

variable (G : Type u) [Group G] [TopologicalSpace G]
variable (H : Subgroup G) (X : Type v) [TopologicalSpace X]
variable [MulAction G X]

/-- If the orbit map of an `H`-fixed point is continuous, its associated algebraic
coset map is continuous. This uses only the quotient topology, not joint
continuity of the action or right-translation continuity of the group. -/
theorem continuous_quotientEquivFixedPoints_symm (x : ↥(MulAction.fixedPoints H X))
    (hx : Continuous (fun g : G => g • x.val)) :
    Continuous (((MulActionHom.quotientEquivFixedPoints G H X).symm
      ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩) : G ⧸ H → X) := by
  apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
  have hcomp :
      (((MulActionHom.quotientEquivFixedPoints G H X).symm
          ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩) : G ⧸ H → X) ∘
          (QuotientGroup.mk : G → G ⧸ H) =
        fun g : G => g • x.val := by
    funext g
    exact MulActionHom.quotientEquivFixedPoints_symm_apply_mk
      ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩ g
  rw [hcomp]
  exact hx

variable [ContinuousSMul G X]

/-- The continuous equivariant map on cosets determined by an `H`-fixed point,
using the algebraic coset-map equivalence. -/
def ofQuotientFixedPoint (x : ↥(MulAction.fixedPoints H X)) :
    ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X :=
  ofMulActionHom
    ((MulActionHom.quotientEquivFixedPoints G H X).symm
      ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩)
    (continuous_quotientEquivFixedPoints_symm G H X x
      (continuous_id.smul continuous_const))

/-- Forgetting continuity recovers the algebraic map associated to the fixed point. -/
@[simp]
theorem ofQuotientFixedPoint_toMulActionHom (x : ↥(MulAction.fixedPoints H X)) :
    (ofQuotientFixedPoint G H X x).toMulActionHom =
      (MulActionHom.quotientEquivFixedPoints G H X).symm
        ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩ := rfl

/-- On the coset represented by `g`, the map associated to `x` has value `g • x`. -/
@[simp]
theorem ofQuotientFixedPoint_apply_mk (x : ↥(MulAction.fixedPoints H X)) (g : G) :
    ofQuotientFixedPoint G H X x (QuotientGroup.mk g) = g • x.val := by
  exact MulActionHom.quotientEquivFixedPoints_symm_apply_mk
    ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩ g

/-- Joint evaluation of the coset maps determined by `H`-fixed points is continuous
when right translations of `G` are continuous and the action on `X` is jointly
continuous. No local compactness or separation assumptions are needed. -/
theorem continuous_uncurry_ofQuotientFixedPoint [ContinuousConstSMul Gᵐᵒᵖ G] :
    Continuous (fun p : ↥(MulAction.fixedPoints H X) × (G ⧸ H) =>
      ofQuotientFixedPoint G H X p.1 p.2) := by
  have hpair : Continuous
      (fun p : ↥(MulAction.fixedPoints H X) × G => (p.2, p.1.val)) :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hsmul : Continuous
      (fun p : ↥(MulAction.fixedPoints H X) × G => p.2 • p.1.val) :=
    (continuous_smul (M := G) (X := X)).comp hpair
  -- Descend in parameter × quotient order, as required for currying.
  have hq := (IsOpenQuotientMap.id (X := ↥(MulAction.fixedPoints H X))).prodMap
    (QuotientGroup.isOpenQuotientMap_mk_of_continuousConstSMul_op H)
  apply hq.isQuotientMap.continuous_iff.mpr
  have hcomp :
      (fun p : ↥(MulAction.fixedPoints H X) × (G ⧸ H) =>
          ofQuotientFixedPoint G H X p.1 p.2) ∘
          Prod.map (@_root_.id ↥(MulAction.fixedPoints H X))
            (QuotientGroup.mk : G → G ⧸ H) =
        fun p : ↥(MulAction.fixedPoints H X) × G => p.2 • p.1.val := by
    funext p
    exact ofQuotientFixedPoint_apply_mk G H X p.1 p.2
  rw [hcomp]
  exact hsmul

/-- The family of coset maps determined by `H`-fixed points is continuous for the
compact-open subspace topology when right translations of `G` are continuous
and the action on `X` is jointly continuous. -/
theorem continuous_ofQuotientFixedPoint [ContinuousConstSMul Gᵐᵒᵖ G] :
    Continuous (ofQuotientFixedPoint G H X) := by
  exact continuous_of_continuous_uncurry (ofQuotientFixedPoint G H X)
    (continuous_uncurry_ofQuotientFixedPoint G H X)

end FixedPointMap

/-- Continuous equivariant maps from `G ⧸ H` correspond homeomorphically to the
`H`-fixed points of `X`. The forward function evaluates at the identity coset;
the inverse sends the coset of `g` to `g • x`.

The topology on maps is induced from the compact-open topology on `C(G ⧸ H, X)`.
The fixed points have the canonical subspace topology of `X`, with the canonical
restricted `H`-action. The subgroup is arbitrary. Continuous right translations
and a jointly continuous action suffice: neither continuous inversion, left
translations, local compactness, separation nor nonemptiness is assumed.
The underlying functions use `MulActionHom.quotientEquivFixedPoints`. -/
def quotientHomeomorphFixedPoints
    (G : Type u) [Group G] [TopologicalSpace G] [ContinuousConstSMul Gᵐᵒᵖ G]
    (H : Subgroup G) (X : Type v) [TopologicalSpace X]
    [MulAction G X] [ContinuousSMul G X] :
    ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X ≃ₜ ↥(MulAction.fixedPoints H X) where
  toEquiv :=
    { toFun := fun f =>
        ⟨(MulActionHom.quotientEquivFixedPoints G H X f.toMulActionHom).val,
          MulAction.mem_fixedPoints_subgroup_iff.mpr
            (MulActionHom.quotientEquivFixedPoints G H X f.toMulActionHom).property⟩
      invFun := ofQuotientFixedPoint G H X
      left_inv := by
        intro f
        apply toMulActionHom_injective
        exact (MulActionHom.quotientEquivFixedPoints G H X).symm_apply_apply
          f.toMulActionHom
      right_inv := by
        intro x
        apply Subtype.ext
        exact (ofQuotientFixedPoint_apply_mk G H X x 1).trans (one_smul G x.val) }
  continuous_toFun := by
    exact
      (continuous_eval_const (F := ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X)
        (QuotientGroup.mk (1 : G))).subtype_mk _
  continuous_invFun := continuous_ofQuotientFixedPoint G H X

section Characteristic

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Subgroup G} {X : Type v} [TopologicalSpace X] [MulAction G X]

/-- Two continuous equivariant coset maps agree if they agree at the identity coset. -/
theorem quotient_ext {f g : ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X}
    (h : f (QuotientGroup.mk (1 : G)) = g (QuotientGroup.mk (1 : G))) : f = g := by
  exact toMulActionHom_injective (MulActionHom.quotient_ext h)

/-- Equality of continuous equivariant coset maps is detected at the identity coset. -/
theorem quotient_ext_iff {f g : ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X} :
    f = g ↔ f (QuotientGroup.mk (1 : G)) = g (QuotientGroup.mk (1 : G)) := by
  exact ⟨fun h => DFunLike.congr_fun h _, quotient_ext⟩

variable [ContinuousConstSMul Gᵐᵒᵖ G] [ContinuousSMul G X]

/-- The homeomorphism evaluates at the identity coset. -/
@[simp]
theorem quotientHomeomorphFixedPoints_apply
    (f : ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X) :
    (quotientHomeomorphFixedPoints G H X f).val = f (QuotientGroup.mk (1 : G)) := rfl

/-- After forgetting continuity, the forward map is the algebraic fixed-point map,
with its fixed-point predicate expressed as stabilizer containment. -/
theorem quotientHomeomorphFixedPoints_forget
    (f : ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X) :
    MulActionHom.quotientEquivFixedPoints G H X f.toMulActionHom =
      ⟨(quotientHomeomorphFixedPoints G H X f).val,
        MulAction.mem_fixedPoints_subgroup_iff.mp
          (quotientHomeomorphFixedPoints G H X f).property⟩ := by
  exact Subtype.ext rfl

/-- The inverse homeomorphism forgets to the original algebraic inverse. -/
@[simp]
theorem quotientHomeomorphFixedPoints_symm_toMulActionHom
    (x : ↥(MulAction.fixedPoints H X)) :
    ((quotientHomeomorphFixedPoints G H X).symm x).toMulActionHom =
      (MulActionHom.quotientEquivFixedPoints G H X).symm
        ⟨x.val, MulAction.mem_fixedPoints_subgroup_iff.mp x.property⟩ := rfl

/-- The inverse homeomorphism sends a representative `g` to `g • x`. -/
@[simp]
theorem quotientHomeomorphFixedPoints_symm_apply_mk
    (x : ↥(MulAction.fixedPoints H X)) (g : G) :
    (quotientHomeomorphFixedPoints G H X).symm x (QuotientGroup.mk g) = g • x.val := by
  exact ofQuotientFixedPoint_apply_mk G H X x g

/-- The inverse gives the unique continuous equivariant map with the specified
value at the identity coset. -/
theorem quotientHomeomorphFixedPoints_symm_eq_iff
    (x : ↥(MulAction.fixedPoints H X))
    (f : ContinuousMulActionHom (@_root_.id G) (G ⧸ H) X) :
    (quotientHomeomorphFixedPoints G H X).symm x = f ↔
      f (QuotientGroup.mk (1 : G)) = x.val := by
  rw [quotient_ext_iff, quotientHomeomorphFixedPoints_symm_apply_mk, one_smul]
  exact eq_comm

end Characteristic

end ContinuousMulActionHom
