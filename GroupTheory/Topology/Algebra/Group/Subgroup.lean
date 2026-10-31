/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Separation.Connected

/-!
# Closure, connected components and finite-index subgroups

The topological closure of a subgroup is a subgroup when multiplication is
separately continuous and inversion is continuous. It is the least closed
subgroup containing the original subgroup, and preserves normality. Joint
continuity and separation assumptions are not needed.

The connected component of the identity is a subgroup already when fixed left
translations are continuous. It is closed and connected, contains every connected
subgroup, and is preserved by continuous homomorphisms between such groups. Their
restrictions to identity-component subgroups are continuous for the subspace
topologies. The subgroup is normal when multiplication is separately continuous.
Neither its subgroup structure nor this normality result needs continuous inversion. The
left-coset space of this subgroup is canonically homeomorphic to the space of
connected components, sending the coset of each element to its component. This
identification gives its index as `Nat.card` of the component space (zero when
infinite), without a finiteness assumption. If there are finitely many components,
this subgroup is open and has finite index, still assuming only continuity of
fixed left translations.

The left-coset projection restricted to a dense set is surjective for any open
subgroup, assuming only continuity of fixed left translations. The proof uses
`Dense.exists_mem_open` on an open left coset. Consequently, restricting an open
subgroup to a dense subgroup preserves its index, without finiteness or normality
assumptions. When open subgroups form a neighborhood basis at the identity,
surjectivity onto all their left-coset spaces conversely characterizes density.
More generally, a point belongs to the closure of a set exactly when its image
belongs to the image of that set in every such left-coset space.

A closed subgroup has finite index if its inverse image in a dense subgroup has
finite index. The finite-index closedness criterion then makes the subgroup open,
still assuming only continuity of fixed left translations. These arguments need
neither normality nor separation assumptions.

`separatelyContinuousMul_of_continuous_const_mul` supplies explicit evidence for
the separate-continuity class from continuous left translations and inversion,
without installing a reverse typeclass instance.

## Implementation notes

The construction extends `Submonoid.topologicalClosure` using `inv_closure`.
It agrees with Mathlib's `Subgroup.topologicalClosure` under the stronger
`IsTopologicalGroup` hypothesis. The locally closed subgroup criterion uses
this shared construction. The component construction uses the canonical regular
action of the given group and generic connected-component image facts. It agrees
with Mathlib's `Subgroup.connectedComponentOfOne` under `IsTopologicalGroup`.
All constructions retain the given group and topology. Finite-index descent uses
a finite union of closed coset fibers containing the dense subgroup. Openness
then follows from `Subgroup.isOpen_iff_isClosed` with the resulting finite-index
instance. The additive closedness criterion uses the canonical `Multiplicative`
transport.

## References

* Mathlib's `Submonoid.topologicalClosure` supplies the multiplication engine.
* Mathlib's `Subgroup.topologicalClosure` and
  `Subgroup.isClosed_of_isLocallyClosed` supply the closure-subgroup argument.
* Mathlib's `Subgroup.connectedComponentOfOne`, `Homeomorph.smul`, and generic
  connected-component maximality and image lemmas supply the component API.
* `GroupTheory.Topology.Algebra.Group.Quotient` supplies the finite-index
  closedness criterion under continuity of fixed left translations.
-/

@[expose] public section

open Topology
open scoped Pointwise

universe u v

/-- A finite-index additive subgroup is open exactly when it is closed, assuming only
continuity of fixed left additions. -/
theorem AddSubgroup.isOpen_iff_isClosed
    {A : Type u} [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    (K : AddSubgroup A) [K.FiniteIndex] : IsOpen (K : Set A) ↔ IsClosed (K : Set A) := by
  have : K.toSubgroup.FiniteIndex :=
    (AddSubgroup.finiteIndex_toSubgroup_iff K).mpr inferInstance
  have : ContinuousConstSMul (Multiplicative A) (Multiplicative A) :=
    ⟨fun a => (continuous_const_vadd a.toAdd : Continuous (fun b : A => a.toAdd + b))⟩
  exact K.toSubgroup.isOpen_iff_isClosed

attribute [to_additive existing] Subgroup.isOpen_iff_isClosed

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Continuous left translations and continuous inversion give separately
continuous multiplication on the same group and topology. This is explicit class
evidence, not a global instance. -/
@[to_additive
/-- Continuous left translations and continuous negation give separately
continuous addition on the same additive group and topology. This is explicit
class evidence, not a global instance. -/]
theorem separatelyContinuousMul_of_continuous_const_mul [ContinuousInv G]
    (h : ∀ a : G, Continuous (fun x : G ↦ a * x)) : SeparatelyContinuousMul G where
  continuous_const_mul := h _
  continuous_mul_const {a} := by
    simpa only [Function.comp_def, mul_inv_rev, inv_inv] using
      continuous_inv.comp ((h a⁻¹).comp continuous_inv)

namespace Subgroup

section SeparateContinuity

variable [SeparatelyContinuousMul G] [ContinuousInv G]

/-- The topological-space closure of a subgroup, assuming only separate
continuity of multiplication and continuity of inversion. -/
@[to_additive
/-- The topological-space closure of an additive subgroup, assuming only separate
continuity of addition and continuity of negation. -/]
def topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) : Subgroup G :=
  { H.toSubmonoid.topologicalClosure with
    inv_mem' := by
      intro x hx
      change x ∈ (_root_.closure (H : Set G))⁻¹
      rwa [inv_closure, inv_coe_set] }

@[to_additive (attr := simp)]
theorem coe_topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) :
    (H.topologicalClosureOfSeparatelyContinuousMul : Set G) = _root_.closure (H : Set G) :=
  rfl

@[to_additive (attr := simp)]
theorem mem_topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) (x : G) :
    x ∈ H.topologicalClosureOfSeparatelyContinuousMul ↔ x ∈ _root_.closure (H : Set G) :=
  Iff.rfl

/-- Every subgroup is contained in its topological closure. -/
@[to_additive /-- Every additive subgroup is contained in its topological closure. -/]
theorem le_topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) :
    H ≤ H.topologicalClosureOfSeparatelyContinuousMul :=
  _root_.subset_closure

/-- The topological closure subgroup has closed carrier. -/
@[to_additive /-- The topological closure additive subgroup has closed carrier. -/]
theorem isClosed_topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) :
    IsClosed (H.topologicalClosureOfSeparatelyContinuousMul : Set G) :=
  isClosed_closure

/-- The topological closure is the least closed subgroup containing the input. -/
@[to_additive
/-- The topological closure is the least closed additive subgroup containing the input. -/]
theorem topologicalClosureOfSeparatelyContinuousMul_le_iff (H : Subgroup G)
    {K : Subgroup G} (hK : IsClosed (K : Set G)) :
    H.topologicalClosureOfSeparatelyContinuousMul ≤ K ↔ H ≤ K := by
  constructor
  · exact H.le_topologicalClosureOfSeparatelyContinuousMul.trans
  · exact fun h ↦ _root_.closure_minimal h hK

/-- Topological closure of subgroups is monotone. -/
@[to_additive /-- Topological closure of additive subgroups is monotone. -/]
theorem topologicalClosureOfSeparatelyContinuousMul_mono {H K : Subgroup G} (h : H ≤ K) :
    H.topologicalClosureOfSeparatelyContinuousMul ≤ K.topologicalClosureOfSeparatelyContinuousMul :=
  _root_.closure_mono h

/-- A closed subgroup equals its topological closure. -/
@[to_additive /-- A closed additive subgroup equals its topological closure. -/]
theorem topologicalClosureOfSeparatelyContinuousMul_eq_self (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : H.topologicalClosureOfSeparatelyContinuousMul = H :=
  le_antisymm ((H.topologicalClosureOfSeparatelyContinuousMul_le_iff hH).mpr le_rfl)
    H.le_topologicalClosureOfSeparatelyContinuousMul

/-- Taking the topological closure subgroup twice has the same result as once. -/
@[to_additive (attr := simp)
/-- Taking the topological closure additive subgroup twice has the same result as once. -/]
theorem topologicalClosureOfSeparatelyContinuousMul_idem (H : Subgroup G) :
    H.topologicalClosureOfSeparatelyContinuousMul.topologicalClosureOfSeparatelyContinuousMul =
      H.topologicalClosureOfSeparatelyContinuousMul :=
  H.topologicalClosureOfSeparatelyContinuousMul.topologicalClosureOfSeparatelyContinuousMul_eq_self
    H.isClosed_topologicalClosureOfSeparatelyContinuousMul

/-- The topological closure of a normal subgroup is normal: conjugation by a
fixed element is continuous already under separate continuity. -/
@[to_additive
/-- The topological closure of a normal additive subgroup is normal: conjugation
by a fixed element is continuous already under separate continuity. -/]
theorem normal_topologicalClosureOfSeparatelyContinuousMul (H : Subgroup G) [H.Normal] :
    H.topologicalClosureOfSeparatelyContinuousMul.Normal where
  conj_mem x hx g := by
    apply map_mem_closure ((continuous_mul_const g⁻¹).comp (continuous_const_mul g)) hx
    exact fun y hy ↦ Subgroup.Normal.conj_mem inferInstance y hy g

end SeparateContinuity

/-- Under joint continuity this construction agrees with Mathlib's topological
closure on the same group, topology and subgroup. -/
@[to_additive
/-- Under joint continuity this construction agrees with Mathlib's topological
closure on the same additive group, topology and subgroup. -/]
theorem topologicalClosureOfSeparatelyContinuousMul_eq_topologicalClosure
    [IsTopologicalGroup G] (H : Subgroup G) :
    H.topologicalClosureOfSeparatelyContinuousMul = H.topologicalClosure := by
  ext x
  rfl

section LeftContinuity

variable [ContinuousConstSMul G G]

/-- The left-coset projection restricted to a dense set is surjective for an open subgroup. -/
@[to_additive
/-- The coset projection restricted to a dense set is surjective for an open additive subgroup. -/]
theorem quotient_mk_surjective_of_dense (H : Subgroup G) (hH : IsOpen (H : Set G))
    {S : Set G} (hS : Dense S) :
    Function.Surjective (fun s : S ↦ (s.val : G ⧸ H)) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hU : IsOpen {x : G | g⁻¹ * x ∈ H} := by
    simpa only [Set.preimage, Homeomorph.smul_apply, smul_eq_mul, SetLike.mem_coe] using
      IsOpen.preimage (Homeomorph.smul (α := G) g⁻¹).continuous hH
  have hg : g⁻¹ * g ∈ H := by
    simpa only [inv_mul_cancel] using H.one_mem
  obtain ⟨s, hs, hsg⟩ := hS.exists_mem_open hU ⟨g, hg⟩
  exact ⟨⟨s, hs⟩, (QuotientGroup.eq.mpr hsg).symm⟩

/-- Restricting an open subgroup to a dense subgroup preserves its index,
without a finiteness assumption. -/
@[to_additive
/-- Restricting an open additive subgroup to a dense additive subgroup preserves
its index, without a finiteness assumption. -/]
theorem index_subgroupOf_eq_of_dense (H : Subgroup G) (hH : IsOpen (H : Set G))
    (D : Subgroup G) (hD : Dense (D : Set G)) :
    (H.subgroupOf D).index = H.index := by
  have hq := H.quotient_mk_surjective_of_dense hH (S := (D : Set G)) hD
  let e : (D ⧸ H.subgroupOf D) ↪
      ((⊤ : Subgroup G) ⧸ H.subgroupOf (⊤ : Subgroup G)) := by
    apply Subgroup.quotientSubgroupOfEmbeddingOfLE
    exact le_top
  have hs : Function.Surjective e := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd⟩ := hq (QuotientGroup.mk (g : G))
    have hmem := QuotientGroup.eq.mp hd
    refine ⟨(QuotientGroup.mk d : D ⧸ H.subgroupOf D), ?_⟩
    dsimp only [e]
    rw [quotientSubgroupOfEmbeddingOfLE_apply_mk]
    exact QuotientGroup.eq.mpr hmem
  have he : (H.subgroupOf D).index =
      (H.subgroupOf (⊤ : Subgroup G)).index :=
    Nat.card_congr (Equiv.ofBijective e ⟨e.injective, hs⟩)
  have hmap : (H.subgroupOf (⊤ : Subgroup G)).map
      (⊤ : Subgroup G).subtype = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, trivial⟩, hx, rfl⟩
  have htop := (⊤ : Subgroup G).index_map_subtype (H.subgroupOf (⊤ : Subgroup G))
  rw [hmap, index_top, Nat.mul_one] at htop
  exact he.trans htop.symm

/-- The connected component of the identity as a subgroup, assuming only continuity
of fixed left translations for the canonical multiplication action. -/
@[to_additive
/-- The connected component of zero as an additive subgroup, assuming only continuity
of fixed left translations for the canonical addition action. -/]
def connectedComponentOfOneOfContinuousConstSMul (G : Type u) [Group G]
    [TopologicalSpace G] [ContinuousConstSMul G G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' {a b} ha hb := by
    have h := (Homeomorph.smul (α := G) a).continuous.image_connectedComponent_subset
      (1 : G) ⟨b, hb, rfl⟩
    simpa only [Homeomorph.smul_apply, smul_eq_mul, mul_one,
      ← connectedComponent_eq ha] using h
  inv_mem' {a} ha := by
    have h := (Homeomorph.smul (α := G) a⁻¹).continuous.image_connectedComponent_subset
      a ⟨1, (connectedComponent_eq ha) ▸ mem_connectedComponent, rfl⟩
    simpa only [Homeomorph.smul_apply, smul_eq_mul, inv_mul_cancel, mul_one] using h

@[to_additive (attr := simp)]
theorem coe_connectedComponentOfOneOfContinuousConstSMul :
    (connectedComponentOfOneOfContinuousConstSMul G : Set G) = connectedComponent (1 : G) :=
  rfl

@[to_additive (attr := simp)]
theorem mem_connectedComponentOfOneOfContinuousConstSMul (x : G) :
    x ∈ connectedComponentOfOneOfContinuousConstSMul G ↔ x ∈ connectedComponent (1 : G) :=
  Iff.rfl

/-- The identity-component subgroup has connected carrier. -/
@[to_additive
/-- The zero-component additive subgroup has connected carrier. -/]
theorem isConnected_connectedComponentOfOneOfContinuousConstSMul :
    IsConnected (connectedComponentOfOneOfContinuousConstSMul G : Set G) :=
  isConnected_connectedComponent

/-- The identity-component subgroup is closed, with no separation assumption. -/
@[to_additive
/-- The zero-component additive subgroup is closed, with no separation assumption. -/]
theorem isClosed_connectedComponentOfOneOfContinuousConstSMul :
    IsClosed (connectedComponentOfOneOfContinuousConstSMul G : Set G) :=
  isClosed_connectedComponent

/-- Every subgroup with preconnected carrier lies in the identity-component subgroup. -/
@[to_additive
/-- Every additive subgroup with preconnected carrier lies in the zero-component subgroup. -/]
theorem le_connectedComponentOfOneOfContinuousConstSMul (H : Subgroup G)
    (hH : IsPreconnected (H : Set G)) :
    H ≤ connectedComponentOfOneOfContinuousConstSMul G :=
  hH.subset_connectedComponent H.one_mem

section Homomorphisms

variable {H : Type v} [Group H] [TopologicalSpace H] [ContinuousConstSMul H H]

/-- A continuous homomorphism sends the identity-component subgroup into the
identity-component subgroup. -/
@[to_additive
/-- A continuous additive homomorphism sends the zero-component subgroup into the
zero-component subgroup. -/]
theorem map_connectedComponentOfOneOfContinuousConstSMul_le (φ : G →* H)
    (hφ : Continuous φ) :
    (connectedComponentOfOneOfContinuousConstSMul G).map φ ≤
      connectedComponentOfOneOfContinuousConstSMul H := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa only [mem_connectedComponentOfOneOfContinuousConstSMul, map_one] using
    hφ.image_connectedComponent_subset (1 : G) ⟨x, hx, rfl⟩

/-- Restrict a continuous homomorphism to the identity-component subgroups. -/
@[to_additive
/-- Restrict a continuous additive homomorphism to the zero-component subgroups. -/]
def _root_.MonoidHom.connectedComponentOfOneMap (φ : G →* H) (hφ : Continuous φ) :
    connectedComponentOfOneOfContinuousConstSMul G →*
      connectedComponentOfOneOfContinuousConstSMul H :=
  (φ.comp (connectedComponentOfOneOfContinuousConstSMul G).subtype).codRestrict
    (connectedComponentOfOneOfContinuousConstSMul H).toSubmonoid
    (fun x ↦ map_connectedComponentOfOneOfContinuousConstSMul_le φ hφ
      ⟨(x : G), x.property, rfl⟩)

@[to_additive (attr := simp)]
theorem _root_.MonoidHom.connectedComponentOfOneMap_apply (φ : G →* H)
    (hφ : Continuous φ) (x : connectedComponentOfOneOfContinuousConstSMul G) :
    (φ.connectedComponentOfOneMap hφ x : H) = φ (x : G) :=
  rfl

/-- The restriction to identity-component subgroups is continuous for their
subspace topologies. -/
@[to_additive
/-- The restriction to zero-component subgroups is continuous for their
subspace topologies. -/]
theorem _root_.MonoidHom.continuous_connectedComponentOfOneMap (φ : G →* H)
    (hφ : Continuous φ) : Continuous (φ.connectedComponentOfOneMap hφ) := by
  exact (hφ.comp continuous_subtype_val).subtype_mk _

end Homomorphisms

/-- Each connected component is a left translate of the identity-component subgroup. -/
@[to_additive
/-- Each connected component is a left translate of the zero-component additive subgroup. -/]
theorem image_mul_connectedComponentOfOneOfContinuousConstSMul (g : G) :
    (fun x : G ↦ g * x) '' (connectedComponentOfOneOfContinuousConstSMul G : Set G) =
      connectedComponent g := by
  simpa only [coe_connectedComponentOfOneOfContinuousConstSMul, Homeomorph.smul_apply,
    smul_eq_mul, mul_one] using
    (Homeomorph.smul (α := G) g).isQuotientMap.image_connectedComponent
      (by simp [isConnected_singleton]) (1 : G)

/-- Left cosets of the identity-component subgroup are canonically the connected
components, with their quotient topologies. No normality assumption is needed. -/
@[to_additive
/-- Left cosets of the zero-component additive subgroup are canonically the connected
components, with their quotient topologies. No normality assumption is needed. -/]
noncomputable def quotientConnectedComponentHomeomorph (G : Type u) [Group G]
    [TopologicalSpace G] [ContinuousConstSMul G G] :
    (G ⧸ connectedComponentOfOneOfContinuousConstSMul G) ≃ₜ ConnectedComponents G where
  toFun := Quotient.lift (fun g : G ↦ (g : ConnectedComponents G)) (by
    intro a b hab
    apply Eq.symm
    apply ConnectedComponents.coe_eq_coe'.mpr
    rw [← image_mul_connectedComponentOfOneOfContinuousConstSMul a]
    exact ⟨a⁻¹ * b, QuotientGroup.eq.mp (Quotient.sound hab), by simp⟩)
  invFun :=
    Quotient.lift (fun g : G ↦ (g : G ⧸ connectedComponentOfOneOfContinuousConstSMul G)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      apply (mem_connectedComponentOfOneOfContinuousConstSMul _).2
      have hb : b ∈ connectedComponent a :=
        ConnectedComponents.coe_eq_coe'.mp (Quotient.sound hab).symm
      have h := (Homeomorph.smul (α := G) a⁻¹).continuous.image_connectedComponent_subset
        a ⟨b, hb, rfl⟩
      simpa only [Homeomorph.smul_apply, smul_eq_mul, inv_mul_cancel] using h)
  left_inv q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  right_inv c := Quotient.inductionOn c fun _ ↦ rfl
  -- Both quotient topologies are coinduced from the representative projections.
  continuous_toFun := continuous_def.mpr fun _ hs ↦ hs
  continuous_invFun := continuous_def.mpr fun _ hs ↦ hs

@[to_additive (attr := simp)]
theorem quotientConnectedComponentHomeomorph_apply (g : G) :
    quotientConnectedComponentHomeomorph G
      (g : G ⧸ connectedComponentOfOneOfContinuousConstSMul G) =
      (g : ConnectedComponents G) :=
  rfl

@[to_additive (attr := simp)]
theorem quotientConnectedComponentHomeomorph_symm_apply (g : G) :
    (quotientConnectedComponentHomeomorph G).symm (g : ConnectedComponents G) =
      (g : G ⧸ connectedComponentOfOneOfContinuousConstSMul G) :=
  rfl

/-- The index of the identity-component subgroup is `Nat.card` of the component
space, which is zero when the component space is infinite. -/
@[to_additive
/-- The index of the zero-component additive subgroup is `Nat.card` of the component
space, which is zero when the component space is infinite. -/]
theorem index_connectedComponentOfOneOfContinuousConstSMul :
    (connectedComponentOfOneOfContinuousConstSMul G).index =
      Nat.card (ConnectedComponents G) :=
  Nat.card_congr (quotientConnectedComponentHomeomorph G).toEquiv

/-- With finitely many connected components, the identity-component subgroup is open.
No separation or local connectedness assumption is needed. -/
@[to_additive
/-- With finitely many connected components, the zero-component additive subgroup is open.
No separation or local connectedness assumption is needed. -/]
theorem isOpen_connectedComponentOfOneOfContinuousConstSMul
    [Finite (ConnectedComponents G)] :
    IsOpen (connectedComponentOfOneOfContinuousConstSMul G : Set G) := by
  simpa only [coe_connectedComponentOfOneOfContinuousConstSMul] using
    (ConnectedComponents.discreteTopology_iff.mp inferInstance (1 : G))

/-- With finitely many connected components, the identity-component subgroup has finite index.
Only continuity of fixed left translations is needed, not normality of the subgroup. -/
@[to_additive
/-- With finitely many connected components, the zero-component additive subgroup has finite
index. Only continuity of fixed left translations is needed, not normality of the subgroup. -/]
instance finiteIndex_connectedComponentOfOneOfContinuousConstSMul
    [Finite (ConnectedComponents G)] :
    (connectedComponentOfOneOfContinuousConstSMul G).FiniteIndex := by
  let e := (quotientConnectedComponentHomeomorph G).toEquiv
  let := Finite.of_surjective e.symm e.symm.surjective
  exact finiteIndex_of_finite_quotient

@[to_additive]
private lemma isClosed_quotient_mk_fiber (N : Subgroup G) (hN : IsClosed (N : Set G))
    (q : G ⧸ N) : IsClosed {g : G | (g : G ⧸ N) = q} := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  have hpreimage :
      {g : G | (g : G ⧸ N) = (a : G ⧸ N)} =
        (Homeomorph.smul (α := G) a⁻¹) ⁻¹' (N : Set G) := by
    ext g
    change ((g : G ⧸ N) = (a : G ⧸ N)) ↔
      (Homeomorph.smul (α := G) a⁻¹) g ∈ N
    rw [eq_comm, QuotientGroup.eq]
    simp only [Homeomorph.smul_apply, smul_eq_mul]
  rw [hpreimage]
  exact hN.preimage (Homeomorph.smul (α := G) a⁻¹).continuous

/-- A closed subgroup has finite index if its inverse image in a dense subgroup
has finite index. Only continuity of fixed left translations is needed. -/
@[to_additive
/-- A closed additive subgroup has finite index if its inverse image in a dense
additive subgroup has finite index. Only continuity of fixed left translations is needed. -/]
theorem finiteIndex_of_isClosed_of_dense_subgroup (N D : Subgroup G)
    (hN : IsClosed (N : Set G)) (hD : Dense (D : Set G))
    [(N.comap D.subtype).FiniteIndex] : N.FiniteIndex := by
  classical
  let Q := D ⧸ N.comap D.subtype
  let f : Q → G ⧸ N := fun q ↦ (((Quotient.out q : D) : G) : G ⧸ N)
  have hclosed : IsClosed (⋃ q : Q, {g : G | (g : G ⧸ N) = f q}) :=
    isClosed_iUnion_of_finite fun q ↦ isClosed_quotient_mk_fiber N hN (f q)
  have hcontains : (D : Set G) ⊆ ⋃ q : Q, {g : G | (g : G ⧸ N) = f q} := by
    intro g hg
    let d : D := ⟨g, hg⟩
    refine Set.mem_iUnion.mpr ⟨(d : Q), ?_⟩
    change (g : G ⧸ N) = f (d : Q)
    apply QuotientGroup.eq.mpr
    change d⁻¹ * Quotient.out (d : Q) ∈ N.comap D.subtype
    exact QuotientGroup.eq.mp (Quotient.out_eq (d : Q)).symm
  have hcover : (Set.univ : Set G) ⊆ ⋃ q : Q, {g : G | (g : G ⧸ N) = f q} := by
    rw [← hD.closure_eq]
    exact _root_.closure_minimal hcontains hclosed
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ g))
    exact ⟨r, hr.symm⟩
  let := Finite.of_surjective f hf
  exact finiteIndex_of_finite_quotient

/-- A closed subgroup is open if its inverse image in a dense subgroup has finite
index. Only continuity of fixed left translations is needed. -/
@[to_additive
/-- A closed additive subgroup is open if its inverse image in a dense additive subgroup
has finite index. Only continuity of fixed left translations is needed. -/]
theorem isOpen_of_isClosed_of_dense_subgroup (N D : Subgroup G)
    (hN : IsClosed (N : Set G)) (hD : Dense (D : Set G))
    [(N.comap D.subtype).FiniteIndex] : IsOpen (N : Set G) := by
  let : N.FiniteIndex := finiteIndex_of_isClosed_of_dense_subgroup N D hN hD
  exact N.isOpen_iff_isClosed.mpr hN

end LeftContinuity

/-- The identity-component subgroup is normal under separate continuity;
continuity of variable inversion is unnecessary. -/
@[to_additive
/-- The zero-component additive subgroup is normal under separate continuity;
continuity of variable negation is unnecessary. -/]
theorem normal_connectedComponentOfOneOfContinuousConstSMul [SeparatelyContinuousMul G] :
    (connectedComponentOfOneOfContinuousConstSMul G).Normal where
  conj_mem x hx g := by
    have h := (IsTopologicalGroup.continuous_conj g).image_connectedComponent_subset
      (1 : G) ⟨x, hx, rfl⟩
    simpa only [mem_connectedComponentOfOneOfContinuousConstSMul, mul_one,
      mul_inv_cancel] using h

/-- Under the stronger topological-group hypotheses, the construction agrees with
Mathlib's identity-component subgroup on the same group and topology. -/
@[to_additive
/-- Under the stronger topological-additive-group hypotheses, the construction agrees
with Mathlib's zero-component subgroup on the same additive group and topology. -/]
theorem connectedComponentOfOneOfContinuousConstSMul_eq_connectedComponentOfOne
    [IsTopologicalGroup G] :
    connectedComponentOfOneOfContinuousConstSMul G = connectedComponentOfOne G := by
  ext x
  rfl

end Subgroup

/-- Closure is detected by images in open-subgroup left-coset quotients. -/
public theorem OpenSubgroup.mem_closure_iff_mem_quotient_image
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (hb : (nhds (1 : G)).HasBasis
      (fun _ : OpenSubgroup G => True) (fun H => (H : Set G)))
    (S : Set G) (x : G) :
    x ∈ closure S ↔ ∀ H : OpenSubgroup G,
      (QuotientGroup.mk x : G ⧸ (H : Subgroup G)) ∈
        (fun y : G => (QuotientGroup.mk y : G ⧸ (H : Subgroup G))) '' S := by
  let e : G ≃ₜ G := Homeomorph.smul (α := G) x
  have e_apply (y : G) : e y = x * y := rfl
  have he : Filter.map e (nhds (1 : G)) = nhds x := by
    simpa only [e_apply, mul_one] using e.map_nhds_eq (1 : G)
  have hx : (nhds x).HasBasis
      (fun _ : OpenSubgroup G => True)
      (fun H => e '' (H : Set G)) := by
    rw [← he]
    exact hb.map e
  rw [mem_closure_iff_frequently, hx.frequently_iff]
  constructor
  · intro h H
    rcases h H trivial with ⟨y, hyH, hyS⟩
    rcases hyH with ⟨z, hz, hzy⟩
    simp only [e_apply] at hzy
    have hxy : x⁻¹ * y ∈ (H : Subgroup G) := by
      rw [← hzy, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hz
    refine ⟨y, hyS, ?_⟩
    exact (QuotientGroup.eq.mpr hxy).symm
  · intro h H _
    rcases h H with ⟨y, hyS, hyq⟩
    have hxy : x⁻¹ * y ∈ (H : Subgroup G) :=
      QuotientGroup.eq.mp hyq.symm
    refine ⟨y, ?_, hyS⟩
    refine ⟨x⁻¹ * y, hxy, ?_⟩
    simp only [e_apply, ← mul_assoc, mul_inv_cancel, one_mul]

/-- A set is dense if it surjects onto every left coset space of an open subgroup,
provided open subgroups form a neighborhood basis at the identity. Only continuity
of fixed left translations is required. -/
theorem dense_of_surjective_openSubgroup_quotients {G : Type u} [Group G]
    [TopologicalSpace G] [ContinuousConstSMul G G]
    (hb : (nhds (1 : G)).HasBasis (fun _ : OpenSubgroup G => True)
      (fun H => (H : Set G))) {S : Set G}
    (hs : ∀ H : OpenSubgroup G, Function.Surjective
      (fun s : S => (QuotientGroup.mk (s : G) : G ⧸ (H : Subgroup G)))) : Dense S := by
  intro x
  apply (OpenSubgroup.mem_closure_iff_mem_quotient_image hb S x).2
  intro H
  obtain ⟨s, hsq⟩ := hs H (QuotientGroup.mk x : G ⧸ (H : Subgroup G))
  exact ⟨(s : G), s.property, hsq⟩

/-- With an open-subgroup neighborhood basis at the identity, density is equivalent
to surjectivity onto every open-subgroup left-coset space. Only continuity of fixed
left translations is needed. -/
theorem dense_iff_surjective_openSubgroup_quotients {G : Type u} [Group G]
    [TopologicalSpace G] [ContinuousConstSMul G G]
    (hb : (nhds (1 : G)).HasBasis (fun _ : OpenSubgroup G => True)
      (fun H => (H : Set G))) {S : Set G} :
    Dense S ↔ ∀ H : OpenSubgroup G, Function.Surjective
      (fun s : S => (QuotientGroup.mk (s : G) : G ⧸ (H : Subgroup G))) := by
  constructor
  · intro hS H
    exact (H : Subgroup G).quotient_mk_surjective_of_dense H.isOpen hS
  · exact dense_of_surjective_openSubgroup_quotients hb
