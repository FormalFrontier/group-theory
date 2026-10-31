/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.LocallyConstant
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Equivariant coset maps and finite-action kernel quotients

For a subgroup `H` of a group `G`, a `G`-equivariant map from the left cosets `G ⧸ H`
to a `G`-set `X` is determined by the image of the identity coset. This image can be any
point fixed by `H`, expressed as the condition `H ≤ MulAction.stabilizer G x`.

`MulActionHom.quotientEquivFixedPoints` realizes this universal property. Its inverse
sends the coset of `g` to `g • x`. No normality of `H` or transitivity of `X` is needed.
The fixed-point subtype need not be stable under `G`, so the result is a plain equivalence.

`MulAction.orbitEquivQuotientStabilizer_smul` and its inverse smul lemma express the
equivariance of Mathlib's existing orbit–stabilizer equivalence, preserving independent
universes for the acting group and the acted-on type.

For another subgroup `K`, `MulActionHom.nonempty_quotient_iff_exists_le_map_conj`
characterizes existence of an equivariant map `G ⧸ H → G ⧸ K` by containment
`H ≤ gKg⁻¹` for some `g : G`. The associated map sends the coset of `x` to the
coset of `x * g`; neither subgroup needs to be normal.

`Action.nonempty_quotient_iso_iff_exists_eq_map_conj` characterizes isomorphisms
of the canonical left-coset actions by conjugacy `H = gKg⁻¹`.
`Action.quotientIsoOfEqMapConj` constructs the isomorphism from a specified
conjugating element and subgroup equality; its inverse sends `[x]` to `[x * g⁻¹]`.
An isomorphism preserves point stabilizers, so evaluating at the identity coset
recovers the conjugate subgroup. Containment alone gives a map, not necessarily
an isomorphism, even for endomorphisms of an infinite coset action.

`MulAction.discreteTopology_quotient_ker_toPermHom` shows that the canonical quotient
by the kernel of an action on a finite T0 space is discrete whenever each orbit map
`g ↦ g • a` is continuous. The given topologies and action are retained, with no
continuity assumption on the group operations and no nonemptiness assumption on the space.

## Implementation notes

The inverse uses Mathlib's `MulAction.ofQuotientStabilizer` after
`Subgroup.quotientMapOfLE`. The fixed-point condition is related to
`MulAction.fixedPoints` by `MulAction.mem_fixedPoints_subgroup_iff`.

The finite-action discreteness theorem reuses
`isLocallyConstant_of_continuous_eval_of_bijective` for the family of action permutations.
Every fiber of the canonical quotient map is a fiber of this locally constant family,
so all quotient singletons are open without using continuity of translations.

## References

These references concern the coset-action results.

The construction uses the coset maps and orbit–stabilizer maps in Mathlib's
`Mathlib.GroupTheory.Coset.Basic` and `Mathlib.GroupTheory.GroupAction.Quotient`,
and the equivariant-map API in `Mathlib.GroupTheory.GroupAction.Hom`.
The existence criterion combines this universal property with Mathlib's stabilizer
formula for a translated point in `Mathlib.GroupTheory.GroupAction.Basic`.
The isomorphism criterion is the coset-action classification in J. P. May,
*A Concise Course in Algebraic Topology*, Chapter 3, §4. Isomorphisms use
Mathlib's `Equiv.toIso` and `Action.mkIso` from its category-of-actions API.
-/

@[expose] public section

universe u v w

namespace MulAction

/-- The canonical quotient by the kernel of an action on a finite T0 space is discrete
if every orbit map `g ↦ g • a` is continuous. No continuity of the group operations
or nonemptiness of the acted-on space is required. -/
theorem discreteTopology_quotient_ker_toPermHom
    {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [Finite A] [T0Space A] [MulAction G A]
    (hcts : ∀ a : A, Continuous (fun g : G => g • a)) :
    DiscreteTopology (G ⧸ (MulAction.toPermHom G A).ker) := by
  let F : G → A → A := fun g a => g • a
  have hbij : ∀ g : G, Function.Bijective (F g) := by
    intro g
    exact ((MulAction.toPermHom G A) g).bijective
  have hF : IsLocallyConstant F :=
    isLocallyConstant_of_continuous_eval_of_bijective G A F hbij hcts
  have hquot (g h : G) :
      (QuotientGroup.mk g : G ⧸ (MulAction.toPermHom G A).ker) =
          QuotientGroup.mk h ↔ F g = F h := by
    rw [QuotientGroup.eq]
    change (MulAction.toPermHom G A) (g⁻¹ * h) = 1 ↔ F g = F h
    rw [map_mul, map_inv, inv_mul_eq_one]
    constructor
    · intro heq
      exact congrArg (fun p : Equiv.Perm A => (p : A → A)) heq
    · intro heq
      apply Equiv.ext
      exact congrFun heq
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  refine Quotient.inductionOn x ?_
  intro g
  change IsOpen {h : G |
    (QuotientGroup.mk h : G ⧸ (MulAction.toPermHom G A).ker) =
      QuotientGroup.mk g}
  have hfiber := (IsLocallyConstant.iff_isOpen_fiber.mp hF) (F g)
  convert hfiber using 1
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hquot]

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

/-- A point is fixed by a subgroup exactly when that subgroup lies in its stabilizer. -/
theorem mem_fixedPoints_subgroup_iff {H : Subgroup G} {x : X} :
    x ∈ fixedPoints H X ↔ H ≤ stabilizer G x := by
  constructor
  · intro hx g hg
    exact hx ⟨g, hg⟩
  · intro hx g
    exact hx g.property

/-- The inverse of the orbit–stabilizer equivalence commutes with the action.
The acting group and the acted-on type may live in independent universes. -/
@[simp]
theorem orbitEquivQuotientStabilizer_symm_smul (x : X) (g : G)
    (q : G ⧸ stabilizer G x) :
    (orbitEquivQuotientStabilizer G x).symm (g • q) =
      g • (orbitEquivQuotientStabilizer G x).symm q := by
  apply Subtype.ext
  exact ofQuotientStabilizer_smul G x g q

/-- The orbit–stabilizer equivalence commutes with the action.
Together with its inverse formula, this makes the existing plain equivalence equivariant;
no new action or orbit carrier is required. -/
@[simp]
theorem orbitEquivQuotientStabilizer_smul (x : X) (g : G) (y : orbit G x) :
    orbitEquivQuotientStabilizer G x (g • y) =
      g • orbitEquivQuotientStabilizer G x y := by
  apply (orbitEquivQuotientStabilizer G x).symm.injective
  rw [Equiv.symm_apply_apply, orbitEquivQuotientStabilizer_symm_smul,
    Equiv.symm_apply_apply]

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

namespace Action

open CategoryTheory

variable {G : Type u} [Group G]

/-- Right translation by `g` identifies the canonical left-coset actions when
`H = gKg⁻¹`. The forward map sends `[z]` to `[z * g]`, and its inverse sends
`[z]` to `[z * g⁻¹]`. Both maps use `MulActionHom.quotientEquivFixedPoints`;
`Action.mkIso` supplies the categorical isomorphism and its inverse equivariance.
No normality or finiteness hypothesis is needed. -/
noncomputable def quotientIsoOfEqMapConj (H K : Subgroup G) (g : G)
    (h : H = K.map (MulAut.conj g).toMonoidHom) :
    Action.ofMulAction G (G ⧸ H) ≅ Action.ofMulAction G (G ⧸ K) := by
  have hfixed : H ≤ MulAction.stabilizer G
      (g • (QuotientGroup.mk (1 : G) : G ⧸ K)) := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]
    exact h.le
  have hinv : K ≤ MulAction.stabilizer G
      (g⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H)) := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]
    intro k hk
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, h]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk
  let f : (G ⧸ H) →[G] (G ⧸ K) :=
    (MulActionHom.quotientEquivFixedPoints G H (G ⧸ K)).symm
      ⟨g • (QuotientGroup.mk (1 : G) : G ⧸ K), hfixed⟩
  let fInv : (G ⧸ K) →[G] (G ⧸ H) :=
    (MulActionHom.quotientEquivFixedPoints G K (G ⧸ H)).symm
      ⟨g⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H), hinv⟩
  have hf (z : G) : f (QuotientGroup.mk z) = QuotientGroup.mk (z * g) := by
    dsimp only [f]
    rw [MulActionHom.quotientEquivFixedPoints_symm_apply_mk]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hfInv (z : G) : fInv (QuotientGroup.mk z) = QuotientGroup.mk (z * g⁻¹) := by
    dsimp only [fInv]
    rw [MulActionHom.quotientEquivFixedPoints_symm_apply_mk]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  let e : (G ⧸ H) ≃ (G ⧸ K) :=
    { toFun := f
      invFun := fInv
      left_inv := by
        intro q
        refine Quotient.inductionOn' q ?_
        intro z
        rw [hf, hfInv]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      right_inv := by
        intro q
        refine Quotient.inductionOn' q ?_
        intro z
        rw [hfInv, hf]
        simp only [mul_assoc, inv_mul_cancel, mul_one] }
  exact Action.mkIso e.toIso fun a => by
    ext q
    exact f.map_smul a q

/-- The forward representative formula for right translation between coset actions. -/
@[simp]
theorem quotientIsoOfEqMapConj_hom_mk (H K : Subgroup G) (g : G)
    (h : H = K.map (MulAut.conj g).toMonoidHom) (z : G) :
    (quotientIsoOfEqMapConj H K g h).hom.hom (QuotientGroup.mk z) =
      QuotientGroup.mk (z * g) := by
  let x : {x : G ⧸ K // H ≤ MulAction.stabilizer G x} :=
    ⟨g • (QuotientGroup.mk (1 : G) : G ⧸ K), by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]
      exact h.le⟩
  change (MulActionHom.quotientEquivFixedPoints G H (G ⧸ K)).symm x
    (QuotientGroup.mk z) = _
  rw [MulActionHom.quotientEquivFixedPoints_symm_apply_mk]
  dsimp only [x]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The inverse representative formula for right translation between coset actions. -/
@[simp]
theorem quotientIsoOfEqMapConj_inv_mk (H K : Subgroup G) (g : G)
    (h : H = K.map (MulAut.conj g).toMonoidHom) (z : G) :
    (quotientIsoOfEqMapConj H K g h).inv.hom (QuotientGroup.mk z) =
      QuotientGroup.mk (z * g⁻¹) := by
  let x : {x : G ⧸ H // K ≤ MulAction.stabilizer G x} :=
    ⟨g⁻¹ • (QuotientGroup.mk (1 : G) : G ⧸ H), by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]
      intro k hk
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, h]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hk⟩
  change (MulActionHom.quotientEquivFixedPoints G K (G ⧸ H)).symm x
    (QuotientGroup.mk z) = _
  rw [MulActionHom.quotientEquivFixedPoints_symm_apply_mk]
  dsimp only [x]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The coset of the chosen conjugating element is the image of the identity coset. -/
theorem quotientIsoOfEqMapConj_hom_one (H K : Subgroup G) (g : G)
    (h : H = K.map (MulAut.conj g).toMonoidHom) :
    (quotientIsoOfEqMapConj H K g h).hom.hom (QuotientGroup.mk (1 : G)) =
      QuotientGroup.mk g := by
  simpa only [one_mul] using quotientIsoOfEqMapConj_hom_mk H K g h 1

/-- The canonical left-coset actions of `G` on `G ⧸ H` and `G ⧸ K` are isomorphic
exactly when `H` and `K` are conjugate (May, *A Concise Course in Algebraic Topology*,
Chapter 3, §4). The image of the identity coset determines a conjugating coset;
no normality or finiteness hypothesis is required. -/
theorem nonempty_quotient_iso_iff_exists_eq_map_conj (H K : Subgroup G) :
    Nonempty (Action.ofMulAction G (G ⧸ H) ≅ Action.ofMulAction G (G ⧸ K)) ↔
      ∃ g : G, H = K.map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨e⟩
    let f : (G ⧸ H) → (G ⧸ K) := e.hom.hom
    have hinj : Function.Injective f :=
      ((CategoryTheory.forget (Action (Type u) G)).mapIso e).toEquiv.injective
    have hequiv (a : G) (q : G ⧸ H) : f (a • q) = a • f q :=
      ConcreteCategory.congr_hom (e.hom.comm a) q
    have hstab : H = MulAction.stabilizer G (f (QuotientGroup.mk (1 : G))) := by
      calc
        H = MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) :=
          (MulAction.stabilizer_quotient H).symm
        _ = MulAction.stabilizer G (f (QuotientGroup.mk (1 : G))) := by
          ext a
          simp only [MulAction.mem_stabilizer_iff, ← hequiv, hinj.eq_iff]
    have hex : ∃ q : G ⧸ K, H = MulAction.stabilizer G q :=
      ⟨f (QuotientGroup.mk (1 : G)), hstab⟩
    rw [QuotientGroup.exists_mk] at hex
    obtain ⟨g, hg⟩ := hex
    refine ⟨g, hg.trans ?_⟩
    simpa only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      MulAction.stabilizer_quotient] using
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g
        (QuotientGroup.mk (1 : G) : G ⧸ K)
  · rintro ⟨g, h⟩
    exact ⟨quotientIsoOfEqMapConj H K g h⟩

end Action
