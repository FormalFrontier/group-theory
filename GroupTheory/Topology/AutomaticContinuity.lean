/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.MulAction
public import GroupTheory.Topology.FiniteIndex
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Automatic continuity of homomorphisms and discrete actions

For a group with a topology and continuous fixed left translations, the following are equivalent:
every finite-index subgroup is open; every homomorphism to a finite discrete group is continuous;
and every algebraic action on a discrete space with finite individual orbits is jointly
continuous. The target and action-carrier universes are independent of the source universe.
Each reverse implication to finite-index openness holds even for an arbitrary source topology,
without continuity of translations or group operations. Subgroups need not be normal, and
finiteness of individual orbits does not require a finite total action image.

The finite-homomorphism reverse implication uses the action on the original left coset set,
encoded in a finite permutation group in the target universe. The preimage of a point stabilizer
is the given subgroup, whereas the permutation homomorphism's kernel is generally its normal
core. Only the auxiliary permutation target is given a discrete topology.

For a compact Hausdorff commutative topological group with a specified dense finitely generated
subgroup, the module also proves continuity of every homomorphism to a compact nonarchimedean
group. The target need not be commutative or Hausdorff, and the homomorphism need not have finite
image. Every action of the same source on an arbitrary discrete space is jointly continuous if
each orbit is finite. The characterizations and their reverse implications also have additive
counterparts for possibly noncommutative additive groups. An additive action requires no additive
structure on its carrier. The compact-source corollaries likewise have additive counterparts.

Openness of all finite-index subgroups descends to finite-index subgroups with their induced
topology and to the factors of binary or arbitrary dependent products. If fixed left
translations are continuous, it ascends from any open subgroup and is stable under binary
and finite dependent products. These stability results also hold for noncommutative additive
groups. Product necessity requires no continuity of group operations.

The proofs use finite-index openness in the source. Orbit–stabilizer makes the original
stabilizers finite-index subgroups. For compact targets, open subgroups have finite index, as do
their algebraic comaps, which test continuity at the identity.

## References

The characterizations use Mathlib's finite-equivalence, permutation, finite-quotient and
orbit–stabilizer APIs, together with the discrete-action stabilizer criterion in
`GroupTheory.Topology.Algebra.MulAction`. The compact-source corollaries combine
`Subgroup.isOpen_of_finiteIndex_of_dense_fg` with Mathlib's compact open-subgroup coset-finiteness,
relative-index comap, nonarchimedean neighborhood-basis and group-homomorphism continuity APIs.
-/

@[expose] public section

open Filter Topology

universe u v

/-- An abstract homomorphism from a compact Hausdorff commutative topological group with a
specified dense finitely generated subgroup to a compact nonarchimedean group is continuous. -/
@[to_additive /-- An abstract additive homomorphism from a compact Hausdorff commutative topological
additive group with a specified dense finitely generated subgroup to a compact nonarchimedean
additive group is continuous. -/]
theorem MonoidHom.continuous_of_dense_fg
    {G : Type u} {H : Type v}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [CompactSpace H] [NonarchimedeanGroup H]
    (f : G →* H) (D : Subgroup G) (hD_fg : D.FG) (hD_dense : Dense (D : Set G)) :
    Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  change Tendsto f (𝓝 (1 : G)) (𝓝 (f 1))
  rw [map_one]
  refine Filter.tendsto_def.mpr ?_
  intro W hW
  obtain ⟨U, hUW⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
  let : U.toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  have hU_rel : U.toSubgroup.IsFiniteRelIndex (⊤ : Subgroup H) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcomap_rel : (U.toSubgroup.comap f).IsFiniteRelIndex (⊤ : Subgroup G) := by
    simpa using Subgroup.IsFiniteRelIndex.comap f hU_rel
  let : (U.toSubgroup.comap f).FiniteIndex :=
    Subgroup.isFiniteRelIndex_top_iff.mp hcomap_rel
  have hopen : IsOpen (U.toSubgroup.comap f : Set G) :=
    Subgroup.isOpen_of_finiteIndex_of_dense_fg D hD_fg hD_dense (U.toSubgroup.comap f)
  exact Filter.mem_of_superset
    (hopen.mem_nhds (show (1 : G) ∈ U.toSubgroup.comap f from
      (U.toSubgroup.comap f).one_mem))
    (fun _ hx => hUW hx)

/-- An abstract action of a compact Hausdorff commutative topological group with a specified
dense finitely generated subgroup on an arbitrary discrete space is jointly continuous if
each orbit is finite. -/
@[to_additive /-- An abstract additive action of a compact Hausdorff commutative
  topological additive group with a specified dense finitely generated subgroup on an arbitrary
  discrete space is jointly
  continuous if each orbit is finite. No additive structure on the carrier is required. -/]
theorem MulAction.continuousSMul_of_finite_orbits_of_dense_fg
    {G : Type u} {β : Type v}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    [TopologicalSpace β] [DiscreteTopology β] [MulAction G β]
    (D : Subgroup G) (hD_fg : D.FG) (hD_dense : Dense (D : Set G))
    (h_orbit : ∀ b : β, (MulAction.orbit G b).Finite) : ContinuousSMul G β := by
  refine MulAction.continuousSMul_iff_stabilizer_isOpen.mpr ?_
  intro b
  let : Finite (MulAction.orbit G b) := (h_orbit b).to_subtype
  let : Finite (G ⧸ MulAction.stabilizer G b) :=
    Finite.of_equiv (MulAction.orbit G b) (MulAction.orbitEquivQuotientStabilizer G b)
  let : (MulAction.stabilizer G b).FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  exact Subgroup.isOpen_of_finiteIndex_of_dense_fg D hD_fg hD_dense (MulAction.stabilizer G b)

/-- Every finite-index subgroup is open if all homomorphisms to finite discrete groups are
continuous. The source topology is arbitrary: no continuity of group operations or translations
is required. The finite targets may lie in an independent universe. -/
theorem Subgroup.isOpen_of_continuous_finite_hom
    {G : Type u} [Group G] [TopologicalSpace G]
    (h : ∀ (H : Type v) [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] (f : G →* H), Continuous f)
    (N : Subgroup G) [N.FiniteIndex] : IsOpen (N : Set G) := by
  classical
  let Q := G ⧸ N
  let : Finite Q := Subgroup.finiteIndex_iff_finite_quotient.mp inferInstance
  let : Fintype Q := Fintype.ofFinite Q
  let D := ULift.{v} (Fin (Fintype.card Q))
  let e : Q ≃ D := (Fintype.equivFin Q).trans Equiv.ulift.symm
  let ρ₀ : G →* Equiv.Perm Q := MulAction.toPermHom G Q
  let ρ : G →* Equiv.Perm D :=
    { toFun := fun g => Equiv.permCongr e (ρ₀ g)
      map_one' := by
        ext d
        simp
      map_mul' := by
        intro a b
        ext d
        simp }
  -- Only the new permutation target is given a discrete topology.
  let : TopologicalSpace (Equiv.Perm D) := ⊥
  let : DiscreteTopology (Equiv.Perm D) := ⟨rfl⟩
  have hρ : Continuous ρ := h (Equiv.Perm D) ρ
  let q₀ : Q := ((1 : G) : G ⧸ N)
  let d₀ : D := e q₀
  -- The point stabilizer, rather than the permutation homomorphism's kernel, recovers N.
  have hmem (g : G) : ρ g d₀ = d₀ ↔ g ∈ N := by
    change e (ρ₀ g (e.symm (e q₀))) = e q₀ ↔ g ∈ N
    rw [e.symm_apply_apply, e.injective.eq_iff]
    change g ∈ MulAction.stabilizer G q₀ ↔ g ∈ N
    rw [show MulAction.stabilizer G q₀ = N from MulAction.stabilizer_quotient N]
  have hpreimage :
      ρ ⁻¹' {σ : Equiv.Perm D | σ d₀ = d₀} = (N : Set G) := by
    ext g
    exact hmem g
  rw [← hpreimage]
  exact (isOpen_discrete _).preimage hρ

private theorem continuous_finite_hom_of_continuousSMul_finite_orbits
    {G : Type u} [Group G] [TopologicalSpace G]
    (h_action : ∀ (β : Type v) [TopologicalSpace β] [DiscreteTopology β] [MulAction G β],
      (∀ b : β, (MulAction.orbit G b).Finite) → ContinuousSMul G β)
    {H : Type v} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    (f : G →* H) : Continuous f := by
  let : MulAction G H := MulAction.compHom H f
  let : ContinuousSMul G H := h_action H (fun _ => Set.toFinite _)
  have h_eval : (fun g : G => g • (1 : H)) = f := by
    funext g
    change f g * 1 = f g
    exact mul_one (f g)
  rw [← h_eval]
  exact continuous_id.smul continuous_const

/-- Every finite-index subgroup is open if every algebraic action on a discrete space with
finite individual orbits is jointly continuous. No continuity of source group operations or
translations is required. The carrier universe is independent of the source universe. -/
theorem Subgroup.isOpen_of_continuousSMul_finite_orbits
    {G : Type u} [Group G] [TopologicalSpace G]
    (h_action : ∀ (β : Type v) [TopologicalSpace β] [DiscreteTopology β] [MulAction G β],
      (∀ b : β, (MulAction.orbit G b).Finite) → ContinuousSMul G β)
    (N : Subgroup G) [N.FiniteIndex] : IsOpen (N : Set G) := by
  exact Subgroup.isOpen_of_continuous_finite_hom
    (fun H _ _ _ _ f =>
      continuous_finite_hom_of_continuousSMul_finite_orbits h_action f) N

/-- All finite-index subgroups are open if and only if every algebraic action on a discrete
space with finite individual orbits is jointly continuous. Only continuity of fixed left
translations on the source is assumed. The carrier universe is independent of the source
universe. -/
theorem isOpen_finiteIndex_iff_continuousSMul_finite_orbits
    (G : Type u) [Group G] [TopologicalSpace G] [ContinuousConstSMul G G] :
    (∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) ↔
      (∀ (β : Type v) [TopologicalSpace β] [DiscreteTopology β] [MulAction G β],
        (∀ b : β, (MulAction.orbit G b).Finite) → ContinuousSMul G β) := by
  constructor
  · intro h_open β _ _ _ h_orbit
    refine MulAction.continuousSMul_iff_stabilizer_isOpen.mpr ?_
    intro b
    let : Finite (MulAction.orbit G b) := (h_orbit b).to_subtype
    let : Finite (G ⧸ MulAction.stabilizer G b) :=
      Finite.of_equiv (MulAction.orbit G b) (MulAction.orbitEquivQuotientStabilizer G b)
    let : (MulAction.stabilizer G b).FiniteIndex :=
      Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
    exact h_open (MulAction.stabilizer G b) inferInstance
  · intro h_action N hN
    let : N.FiniteIndex := hN
    exact Subgroup.isOpen_of_continuousSMul_finite_orbits h_action N

/-- All finite-index subgroups are open if and only if every homomorphism to a finite discrete
group is continuous. Only continuity of fixed left translations on the source is assumed.
The finite target universe is independent of the source universe. -/
theorem isOpen_finiteIndex_iff_continuous_finite_hom
    (G : Type u) [Group G] [TopologicalSpace G] [ContinuousConstSMul G G] :
    (∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) ↔
      (∀ (H : Type v) [Group H] [TopologicalSpace H] [DiscreteTopology H]
        [Finite H] (f : G →* H), Continuous f) := by
  constructor
  · intro h_open H _ _ _ _ f
    exact continuous_finite_hom_of_continuousSMul_finite_orbits
      ((isOpen_finiteIndex_iff_continuousSMul_finite_orbits.{u, v} G).mp h_open) f
  · intro h_hom N hN
    let : N.FiniteIndex := hN
    exact Subgroup.isOpen_of_continuous_finite_hom h_hom N

/-- Every finite-index additive subgroup is open if all additive homomorphisms to finite discrete
additive groups are continuous. The source topology is arbitrary: no continuity of addition,
negation or translations is required. The finite targets may lie in an independent universe. -/
theorem AddSubgroup.isOpen_of_continuous_finite_addHom
    {A : Type u} [AddGroup A] [TopologicalSpace A]
    (h : ∀ (B : Type v) [AddGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [Finite B] (f : A →+ B), Continuous f)
    (N : AddSubgroup A) [N.FiniteIndex] : IsOpen (N : Set A) := by
  classical
  let Q := A ⧸ N
  let : Finite Q := AddSubgroup.finiteIndex_iff_finite_quotient.mp inferInstance
  let : Fintype Q := Fintype.ofFinite Q
  let D := ULift.{v} (Fin (Fintype.card Q))
  let e : Q ≃ D := (Fintype.equivFin Q).trans Equiv.ulift.symm
  let τ (a : A) : Equiv.Perm Q := AddAction.toPerm a
  let ρ : A →+ Additive (Equiv.Perm D) :=
    { toFun := fun a => Additive.ofMul (Equiv.permCongr e (τ a))
      map_zero' := by
        change Equiv.permCongr e (τ 0) = 1
        ext d
        simp [τ]
      map_add' := by
        intro a b
        change Equiv.permCongr e (τ (a + b)) =
          Equiv.permCongr e (τ a) * Equiv.permCongr e (τ b)
        ext d
        simp [τ, add_vadd] }
  -- Addition in this new target is permutation composition, without commutativity.
  let : Finite (Additive (Equiv.Perm D)) :=
    Finite.of_equiv (Equiv.Perm D) Additive.ofMul
  let : TopologicalSpace (Additive (Equiv.Perm D)) := ⊥
  let : DiscreteTopology (Additive (Equiv.Perm D)) := ⟨rfl⟩
  have hρ : Continuous ρ := h (Additive (Equiv.Perm D)) ρ
  let q₀ : Q := ((0 : A) : A ⧸ N)
  let d₀ : D := e q₀
  have hmem (a : A) : Additive.toMul (ρ a) d₀ = d₀ ↔ a ∈ N := by
    change e (a +ᵥ e.symm (e q₀)) = e q₀ ↔ a ∈ N
    rw [e.symm_apply_apply, e.injective.eq_iff]
    change a ∈ AddAction.stabilizer A q₀ ↔ a ∈ N
    rw [show AddAction.stabilizer A q₀ = N from AddAction.stabilizer_quotient N]
  have hpreimage :
      ρ ⁻¹' {σ : Additive (Equiv.Perm D) | Additive.toMul σ d₀ = d₀} = (N : Set A) := by
    ext a
    exact hmem a
  rw [← hpreimage]
  exact (isOpen_discrete _).preimage hρ

private theorem continuousVAdd_of_isOpen_finiteIndex
    {A : Type u} {β : Type v}
    [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    [TopologicalSpace β] [DiscreteTopology β] [AddAction A β]
    (h_open : ∀ (N : AddSubgroup A), N.FiniteIndex → IsOpen (N : Set A))
    (h_orbit : ∀ b : β, (AddAction.orbit A b).Finite) : ContinuousVAdd A β := by
  refine AddAction.continuousVAdd_iff_stabilizer_isOpen.mpr ?_
  intro b
  let : Finite (AddAction.orbit A b) := (h_orbit b).to_subtype
  let : Finite (A ⧸ AddAction.stabilizer A b) :=
    Finite.of_equiv (AddAction.orbit A b) (AddAction.orbitEquivQuotientStabilizer A b)
  let : (AddAction.stabilizer A b).FiniteIndex :=
    AddSubgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  exact h_open (AddAction.stabilizer A b) inferInstance

private theorem continuous_finite_addHom_of_continuousVAdd_finite_orbits
    {A : Type u} [AddGroup A] [TopologicalSpace A]
    (h_action : ∀ (β : Type v) [TopologicalSpace β] [DiscreteTopology β] [AddAction A β],
      (∀ b : β, (AddAction.orbit A b).Finite) → ContinuousVAdd A β)
    {B : Type v} [AddGroup B] [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    (f : A →+ B) : Continuous f := by
  let : AddAction A B := AddAction.compHom B f
  let : ContinuousVAdd A B := h_action B (fun b => Set.toFinite (AddAction.orbit A b))
  have hf : Continuous (fun a : A => a +ᵥ (0 : B)) := continuous_id.vadd continuous_const
  change Continuous (fun a : A => f a + 0) at hf
  simpa using hf

/-- Every finite-index additive subgroup is open if all actions on discrete spaces with finite
individual orbits are jointly continuous. The source topology is arbitrary: no continuity of
addition, negation or translations is required. Carriers may lie in an independent universe. -/
theorem AddSubgroup.isOpen_of_continuousVAdd_finite_orbits
    {A : Type u} [AddGroup A] [TopologicalSpace A]
    (h_action : ∀ (β : Type v) [TopologicalSpace β] [DiscreteTopology β] [AddAction A β],
      (∀ b : β, (AddAction.orbit A b).Finite) → ContinuousVAdd A β)
    (N : AddSubgroup A) [N.FiniteIndex] : IsOpen (N : Set A) := by
  have h_hom : ∀ (B : Type v) [AddGroup B] [TopologicalSpace B] [DiscreteTopology B]
      [Finite B] (f : A →+ B), Continuous f := by
    intro B _ _ _ _ f
    exact continuous_finite_addHom_of_continuousVAdd_finite_orbits h_action f
  exact N.isOpen_of_continuous_finite_addHom h_hom

/-- If every fixed left addition is continuous, openness of all finite-index additive subgroups
is equivalent to continuity of all additive homomorphisms to finite discrete additive groups.
The target universe is independent of the source universe. -/
theorem isOpen_finiteIndex_iff_continuous_finite_addHom
    (A : Type u) [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A] :
    (∀ (N : AddSubgroup A), N.FiniteIndex → IsOpen (N : Set A)) ↔
      (∀ (B : Type v) [AddGroup B] [TopologicalSpace B] [DiscreteTopology B]
        [Finite B] (f : A →+ B), Continuous f) := by
  constructor
  · intro h_open B _ _ _ _ f
    apply continuous_finite_addHom_of_continuousVAdd_finite_orbits (f := f)
    intro β _ _ _ h_orbit
    exact continuousVAdd_of_isOpen_finiteIndex h_open h_orbit
  · intro h N hN
    let : N.FiniteIndex := hN
    exact N.isOpen_of_continuous_finite_addHom h

universe w

/-- If every fixed left addition is continuous, openness of all finite-index additive subgroups
is equivalent to joint continuity of every action on a discrete space whose individual orbits
are finite. The carrier needs no additive structure and may lie in an independent universe. -/
theorem isOpen_finiteIndex_iff_continuousVAdd_finite_orbits
    (A : Type u) [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A] :
    (∀ (N : AddSubgroup A), N.FiniteIndex → IsOpen (N : Set A)) ↔
      (∀ (β : Type w) [TopologicalSpace β] [DiscreteTopology β] [AddAction A β],
        (∀ b : β, (AddAction.orbit A b).Finite) → ContinuousVAdd A β) := by
  constructor
  · intro h_open β _ _ _ h_orbit
    exact continuousVAdd_of_isOpen_finiteIndex h_open h_orbit
  · intro h_action N hN
    let : N.FiniteIndex := hN
    exact N.isOpen_of_continuousVAdd_finite_orbits h_action

/-! ## Finite-index openness and open subgroups -/

/-- Openness of every finite-index subgroup descends to a finite-index subgroup with its
induced topology. No continuity of group operations or translations is required. -/
@[to_additive /-- Openness of every finite-index additive subgroup descends to a finite-index
additive subgroup with its induced topology. No continuity of addition, negation or translations
is required. -/]
theorem Subgroup.isOpen_finiteIndex_of_finiteIndex
    {G : Type u} [Group G] [TopologicalSpace G]
    (H : Subgroup G) [H.FiniteIndex]
    (hG : ∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) :
    ∀ (K : Subgroup H), K.FiniteIndex → IsOpen (K : Set H) := by
  intro K hK
  let : K.FiniteIndex := hK
  let : (K.map H.subtype).FiniteIndex := Subgroup.finiteIndex_iff.mpr (by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero (Subgroup.finiteIndex_iff.mp hK)
      (Subgroup.finiteIndex_iff.mp (inferInstance : H.FiniteIndex)))
  have hpre : H.subtype ⁻¹' (K.map H.subtype : Set G) = (K : Set H) := by
    rw [Subgroup.coe_map]
    exact Set.preimage_image_eq _ H.subtype_injective
  rw [← hpre]
  exact (hG (K.map H.subtype) inferInstance).preimage continuous_subtype_val

/-- If every finite-index subgroup of an open subgroup is open in its induced topology,
then every finite-index subgroup of the ambient group is open. Only continuity of fixed left
translations is required, and the open subgroup need not have finite index. -/
@[to_additive /-- If every finite-index additive subgroup of an open additive subgroup is open
in its induced topology, then every finite-index additive subgroup of the ambient additive
group is open. Only continuity of fixed left additions is required, and the open additive
subgroup need not have finite index. -/]
theorem Subgroup.isOpen_finiteIndex_of_isOpen
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hH_open : ∀ (K : Subgroup H), K.FiniteIndex → IsOpen (K : Set H)) :
    ∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G) := by
  intro N hN
  let : N.FiniteIndex := hN
  have hNH : IsOpen ((N ⊓ H : Subgroup G) : Set G) := by
    rw [← Subgroup.subgroupOf_map_subtype N H, Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ (hH_open _ inferInstance)
  exact N.isOpen_iff_mem_nhds_one.mpr
    (Filter.mem_of_superset (hNH.mem_nhds (N ⊓ H).one_mem) (fun _ hx => hx.1))

/-- For a finite-index subgroup, openness of every ambient finite-index subgroup is equivalent
to openness of the subgroup together with openness of all its finite-index subgroups in the
induced topology. Only continuity of fixed left translations is required. -/
@[to_additive /-- For a finite-index additive subgroup, openness of every ambient finite-index
additive subgroup is equivalent to openness of the additive subgroup together with openness of
all its finite-index additive subgroups in the induced topology. Only continuity of fixed left
additions is required. -/]
theorem Subgroup.isOpen_finiteIndex_iff_of_finiteIndex
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) [H.FiniteIndex] :
    (∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) ↔
      IsOpen (H : Set G) ∧
        (∀ (K : Subgroup H), K.FiniteIndex → IsOpen (K : Set H)) := by
  constructor
  · intro hG
    exact ⟨hG H inferInstance, H.isOpen_finiteIndex_of_finiteIndex hG⟩
  · rintro ⟨hH, hH_open⟩
    exact H.isOpen_finiteIndex_of_isOpen hH hH_open

section FiniteIndexProducts

attribute [to_additive existing AddSubgroup.isOpen_of_continuous_finite_addHom]
  Subgroup.isOpen_of_continuous_finite_hom
attribute [to_additive existing isOpen_finiteIndex_iff_continuous_finite_addHom]
  isOpen_finiteIndex_iff_continuous_finite_hom

/-- If every finite-index subgroup of a product is open, the same holds in each factor.
No continuity of multiplication or translations is required. -/
@[to_additive AddSubgroup.isOpen_finiteIndex_factors_of_prod
  /-- If every finite-index additive subgroup of a product is open, the same holds in each
  factor. No continuity of addition or translations is required. -/]
theorem Subgroup.isOpen_finiteIndex_factors_of_prod
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (hGH : ∀ (N : Subgroup (G × H)),
      N.FiniteIndex → IsOpen (N : Set (G × H))) :
    (∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) ∧
      (∀ (N : Subgroup H), N.FiniteIndex → IsOpen (N : Set H)) := by
  constructor
  · intro N hN
    let : N.FiniteIndex := hN
    have hrel : (N.comap (MonoidHom.fst G H)).IsFiniteRelIndex ⊤ := by
      simpa using Subgroup.IsFiniteRelIndex.comap (MonoidHom.fst G H)
        (show N.IsFiniteRelIndex ⊤ from Subgroup.isFiniteRelIndex_of_finiteIndex)
    have hfinite : (N.comap (MonoidHom.fst G H)).FiniteIndex :=
      Subgroup.isFiniteRelIndex_top_iff.mp hrel
    exact (hGH _ hfinite).preimage
      (show Continuous (fun g : G => (g, (1 : H))) from
        continuous_id.prodMk continuous_const)
  · intro N hN
    let : N.FiniteIndex := hN
    have hrel : (N.comap (MonoidHom.snd G H)).IsFiniteRelIndex ⊤ := by
      simpa using Subgroup.IsFiniteRelIndex.comap (MonoidHom.snd G H)
        (show N.IsFiniteRelIndex ⊤ from Subgroup.isFiniteRelIndex_of_finiteIndex)
    have hfinite : (N.comap (MonoidHom.snd G H)).FiniteIndex :=
      Subgroup.isFiniteRelIndex_top_iff.mp hrel
    exact (hGH _ hfinite).preimage
      (show Continuous (fun h : H => ((1 : G), h)) from
        continuous_const.prodMk continuous_id)

/-- If every finite-index subgroup of each factor is open, the same holds in the product,
provided fixed left translations are continuous in each factor. -/
@[to_additive AddSubgroup.isOpen_finiteIndex_prod
  /-- If every finite-index additive subgroup of each factor is open, the same holds in the
  product, provided fixed left translations are continuous in each factor. -/]
theorem Subgroup.isOpen_finiteIndex_prod
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    [Group H] [TopologicalSpace H] [ContinuousConstSMul H H]
    (hG : ∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G))
    (hH : ∀ (N : Subgroup H), N.FiniteIndex → IsOpen (N : Set H)) :
    ∀ (N : Subgroup (G × H)), N.FiniteIndex → IsOpen (N : Set (G × H)) := by
  intro N hN
  let : N.FiniteIndex := hN
  refine Subgroup.isOpen_of_continuous_finite_hom.{max u v, 0} ?_ N
  intro F _ _ _ _ f
  have hleft : Continuous (f.comp (MonoidHom.inl G H)) :=
    (isOpen_finiteIndex_iff_continuous_finite_hom G).mp hG F
      (f.comp (MonoidHom.inl G H))
  have hright : Continuous (f.comp (MonoidHom.inr G H)) :=
    (isOpen_finiteIndex_iff_continuous_finite_hom H).mp hH F
      (f.comp (MonoidHom.inr G H))
  -- The order of the factors is preserved even when the target is noncommutative.
  have hmul : Continuous (fun p : G × H => f (p.1, 1) * f (1, p.2)) :=
    (hleft.comp continuous_fst).mul (hright.comp continuous_snd)
  simpa only [← map_mul, Prod.fst_mul_snd] using hmul

/-- With continuous fixed left translations in each factor, every finite-index subgroup of a
product is open if and only if the same holds in both factors. -/
@[to_additive AddSubgroup.isOpen_finiteIndex_prod_iff
  /-- With continuous fixed left translations in each factor, every finite-index additive
  subgroup of a product is open if and only if the same holds in both factors. -/]
theorem Subgroup.isOpen_finiteIndex_prod_iff
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    [Group H] [TopologicalSpace H] [ContinuousConstSMul H H] :
    (∀ (N : Subgroup (G × H)), N.FiniteIndex → IsOpen (N : Set (G × H))) ↔
      (∀ (N : Subgroup G), N.FiniteIndex → IsOpen (N : Set G)) ∧
        (∀ (N : Subgroup H), N.FiniteIndex → IsOpen (N : Set H)) :=
  ⟨Subgroup.isOpen_finiteIndex_factors_of_prod,
    fun h => Subgroup.isOpen_finiteIndex_prod h.1 h.2⟩

end FiniteIndexProducts

/-!
## Dependent products

Finite-index openness descends from an arbitrary dependent product to every factor. For a
finite index type it also ascends from the factors when their fixed left translations are
continuous. The finite-product argument uses Mathlib's `Subgroup.pi_le_iff` for the subgroup
rectangle inclusion, and `Subgroup.coe_pi` and `isOpen_set_pi` for its openness.
-/

/-- If all finite-index subgroups of a dependent product are open, then all finite-index
subgroups of each factor are open. The index type and the factor topologies are arbitrary. -/
@[to_additive /-- If all finite-index additive
subgroups of a dependent product are open, then all finite-index additive subgroups of each
factor are open. The index type and the factor topologies are arbitrary. -/]
theorem Subgroup.isOpen_finiteIndex_factors_of_pi
    {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (hPi : ∀ (N : Subgroup (∀ i, G i)),
      N.FiniteIndex → IsOpen (N : Set (∀ i, G i))) :
    ∀ i, ∀ (N : Subgroup (G i)), N.FiniteIndex → IsOpen (N : Set (G i)) := by
  classical
  intro i N hN
  let : N.FiniteIndex := hN
  have hN_rel : N.IsFiniteRelIndex (⊤ : Subgroup (G i)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcomap_rel : (N.comap (Pi.evalMonoidHom G i)).IsFiniteRelIndex
      (⊤ : Subgroup (∀ i, G i)) := by
    simpa using Subgroup.IsFiniteRelIndex.comap (Pi.evalMonoidHom G i) hN_rel
  have hopen : IsOpen (N.comap (Pi.evalMonoidHom G i) : Set (∀ i, G i)) :=
    hPi _ (Subgroup.isFiniteRelIndex_top_iff.mp hcomap_rel)
  simpa [Subgroup.coe_comap, Set.preimage, Pi.mulSingle_eq_same] using
    hopen.preimage (continuous_mulSingle (A := G) i)

/-- All finite-index subgroups of a finite dependent product are open if all finite-index
subgroups of each factor are open and each fixed left translation in a factor is continuous. -/
@[to_additive /-- All finite-index additive subgroups of a
finite dependent product are open if all finite-index additive subgroups of each factor are
open and each fixed left addition in a factor is continuous. -/]
theorem Subgroup.isOpen_finiteIndex_pi
    {ι : Type u} {G : ι → Type v} [Finite ι]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, ContinuousConstSMul (G i) (G i)]
    (hG : ∀ i, ∀ (N : Subgroup (G i)),
      N.FiniteIndex → IsOpen (N : Set (G i))) :
    ∀ (N : Subgroup (∀ i, G i)), N.FiniteIndex → IsOpen (N : Set (∀ i, G i)) := by
  classical
  intro N hN
  let : N.FiniteIndex := hN
  let K : ∀ i, Subgroup (G i) := fun i => N.comap (MonoidHom.mulSingle G i)
  have hK (i : ι) : (K i).FiniteIndex := by
    refine Subgroup.isFiniteRelIndex_top_iff.mp ?_
    have hN_rel : N.IsFiniteRelIndex (⊤ : Subgroup (∀ i, G i)) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex
    simpa [K] using Subgroup.IsFiniteRelIndex.comap (MonoidHom.mulSingle G i) hN_rel
  have hrect_open : IsOpen (Subgroup.pi Set.univ K : Set (∀ i, G i)) := by
    rw [Subgroup.coe_pi]
    exact isOpen_set_pi (Set.toFinite Set.univ) (fun i _ => hG i (K i) (hK i))
  have hrect_le : Subgroup.pi Set.univ K ≤ N := by
    refine Subgroup.pi_le_iff.mpr ?_
    intro i
    exact Subgroup.map_comap_le (MonoidHom.mulSingle G i) N
  -- Use the canonical self-action, with continuity proved coordinatewise.
  let : ContinuousConstSMul (∀ i, G i) (∀ i, G i) := ⟨fun g => by
    change Continuous (fun x : ∀ i, G i => fun i => g i * x i)
    exact continuous_pi fun i =>
      (continuous_const_smul (g i)).comp (continuous_apply i)⟩
  refine (N.isOpen_iff_mem_nhds_one).mpr ?_
  exact Filter.mem_of_superset
    (hrect_open.mem_nhds (Subgroup.pi Set.univ K).one_mem) hrect_le

/-- For a finite dependent product whose factors have continuous fixed left translations,
all finite-index subgroups are open if and only if this holds in every factor. -/
@[to_additive /-- For a finite dependent product whose
factors have continuous fixed left additions, all finite-index additive subgroups are open
if and only if this holds in every factor. -/]
theorem Subgroup.isOpen_finiteIndex_pi_iff
    {ι : Type u} {G : ι → Type v} [Finite ι]
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, ContinuousConstSMul (G i) (G i)] :
    (∀ (N : Subgroup (∀ i, G i)), N.FiniteIndex → IsOpen (N : Set (∀ i, G i))) ↔
      (∀ i, ∀ (N : Subgroup (G i)), N.FiniteIndex → IsOpen (N : Set (G i))) :=
  ⟨Subgroup.isOpen_finiteIndex_factors_of_pi, Subgroup.isOpen_finiteIndex_pi⟩
