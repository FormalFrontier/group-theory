/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.MulAction
public import GroupTheory.Topology.FiniteIndex
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
