/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.GroupAction.Orbit
public import GroupTheory.GroupAction.Quotient
public import GroupTheory.Topology.SeparateContinuity
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Joint continuity and orbit–stabilizer quotients

A finite neighborhood in the right factor gives a pointwise criterion for joint
continuity from continuity of its rows and column. In particular, separate
continuity implies joint continuity when every point of the right factor has a
finite neighborhood, including for scalar multiplication.

A space with a pretransitive group action by continuous maps is R₀ if it contains
a nonempty closed compact subset. In particular, a compact space with such an
action is R₀, and a finite T₀ space with such an action is discrete. The latter
also applies to finite orbits whose subtype topologies are T₀, without separation
assumptions on the ambient space.

A discrete orbit is homeomorphic to the left-coset quotient by its stabilizer when
its orbit map is continuous. The orbit has its subtype topology, and the quotient
has its coinduced topology.

The construction promotes Mathlib's orbit–stabilizer equivalence without
changing its underlying maps.
-/

@[expose] public section

universe u v w

open scoped Topology

private theorem exists_minimal_nonempty_closed_subset_of_isCompact
    {X : Type v} [TopologicalSpace X] {K : Set X}
    (hKne : K.Nonempty) (hKclosed : IsClosed K) (hKcompact : IsCompact K) :
    ∃ C : Set X, C ⊆ K ∧ C.Nonempty ∧ IsClosed C ∧
      ∀ D : Set X, D ⊆ C → D.Nonempty → IsClosed D → C ⊆ D := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hUne : (Set.univ : Set K).Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    exact ⟨⟨x, hx⟩, Set.mem_univ _⟩
  obtain ⟨E, _, hEne, hEclosed, hEmin⟩ :=
    (isClosed_univ : IsClosed (Set.univ : Set K)).exists_minimal_nonempty_closed_subset hUne
  obtain ⟨F, hFclosed, hFE⟩ :
      ∃ F : Set X, IsClosed F ∧ (Subtype.val ⁻¹' F : Set K) = E :=
    isClosed_induced_iff.mp hEclosed
  refine ⟨K ∩ F, Set.inter_subset_left, ?_, hKclosed.inter hFclosed, ?_⟩
  · obtain ⟨x, hx⟩ := hEne
    refine ⟨x, x.property, ?_⟩
    have hxF : x ∈ (Subtype.val ⁻¹' F : Set K) := by rwa [hFE]
    exact hxF
  · intro D hDC hDne hDclosed
    have hDpre : (Subtype.val ⁻¹' D : Set K) ⊆ E := by
      intro x hx
      rw [← hFE]
      exact (hDC hx).2
    have hDpre_ne : (Subtype.val ⁻¹' D : Set K).Nonempty := by
      obtain ⟨x, hx⟩ := hDne
      exact ⟨⟨x, (hDC hx).1⟩, hx⟩
    have hED := hEmin _ hDpre hDpre_ne (hDclosed.preimage continuous_subtype_val)
    intro x hx
    have hxE : (⟨x, hx.1⟩ : K) ∈ E := by
      rw [← hFE]
      exact hx.2
    rw [← hED] at hxE
    exact hxE

namespace MulAction

private theorem closure_singleton_minimal_of_isPretransitive
    (G : Type u) [Group G] {X : Type v} [TopologicalSpace X]
    [MulAction G X] [IsPretransitive G X] [ContinuousConstSMul G X]
    {C : Set X} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCmin : ∀ D : Set X, D ⊆ C → D.Nonempty → IsClosed D → C ⊆ D)
    (x : X) :
    ∀ D : Set X, D ⊆ closure ({x} : Set X) → D.Nonempty → IsClosed D →
      closure ({x} : Set X) ⊆ D := by
  obtain ⟨c, hc⟩ := hCne
  obtain ⟨g, hg⟩ := exists_smul_eq G c x
  let e : X ≃ₜ X := Homeomorph.smul g
  let T : Set X := e.symm ⁻¹' C
  have hec : e c = x := hg
  have hxT : x ∈ T := by
    change e.symm x ∈ C
    rw [← hec, e.symm_apply_apply]
    exact hc
  have hTmin : ∀ D : Set X, D ⊆ T → D.Nonempty → IsClosed D → T ⊆ D := by
    intro D hDT hDne hDclosed
    have hCD : C ⊆ e ⁻¹' D :=
      hCmin (e ⁻¹' D)
        (by
          intro z hz
          have hz' := hDT hz
          change e.symm (e z) ∈ C at hz'
          simpa only [e.symm_apply_apply] using hz')
        (by
          obtain ⟨z, hz⟩ := hDne
          refine ⟨e.symm z, ?_⟩
          change e (e.symm z) ∈ D
          simpa only [e.apply_symm_apply] using hz)
        (hDclosed.preimage e.continuous)
    intro z hz
    have hz' := hCD hz
    change e (e.symm z) ∈ D at hz'
    simpa only [e.apply_symm_apply] using hz'
  have hclosure : closure ({x} : Set X) ⊆ T :=
    closure_minimal (Set.singleton_subset_iff.mpr hxT)
      (hCclosed.preimage e.symm.continuous)
  intro D hD hDne hDclosed
  exact hclosure.trans (hTmin D (hD.trans hclosure) hDne hDclosed)

/-- A pretransitive group action by continuous maps makes a space R₀ whenever it
contains a nonempty closed compact subset. -/
theorem r0Space_of_isPretransitive_of_isCompact_of_isClosed
    (G : Type u) [Group G] {X : Type v} [TopologicalSpace X]
    [MulAction G X] [IsPretransitive G X]
    (hcts : ∀ g : G, Continuous (fun x : X => g • x))
    {K : Set X} (hKne : K.Nonempty) (hKclosed : IsClosed K)
    (hKcompact : IsCompact K) : R0Space X := by
  let : ContinuousConstSMul G X := ⟨hcts⟩
  obtain ⟨C, _, hCne, hCclosed, hCmin⟩ :=
    exists_minimal_nonempty_closed_subset_of_isCompact hKne hKclosed hKcompact
  have hsymm (x y : X) (hxy : closure ({x} : Set X) ⊆ closure ({y} : Set X)) :
      closure ({y} : Set X) ⊆ closure ({x} : Set X) :=
    closure_singleton_minimal_of_isPretransitive G hCne hCclosed hCmin y
      (closure ({x} : Set X)) hxy ⟨x, subset_closure (by simp)⟩ isClosed_closure
  refine ⟨⟨?_⟩⟩
  intro x y hxy
  rw [specializes_iff_closure_subset] at hxy ⊢
  exact hsymm _ _ hxy

/-- A compact space with a pretransitive group action by continuous maps is R₀. -/
theorem r0Space_of_compactSpace_of_isPretransitive
    (G : Type u) [Group G] {X : Type v} [TopologicalSpace X] [CompactSpace X]
    [MulAction G X] [IsPretransitive G X]
    (hcts : ∀ g : G, Continuous (fun x : X => g • x)) : R0Space X := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    exact r0Space_of_isPretransitive_of_isCompact_of_isClosed G hcts
      (K := Set.univ) ⟨x, Set.mem_univ x⟩ isClosed_univ isCompact_univ
  · refine ⟨⟨?_⟩⟩
    intro x
    exact (hX ⟨x⟩).elim

/-- A finite T₀ space with a pretransitive group action by continuous maps is discrete. -/
theorem discreteTopology_of_finite_of_isPretransitive
    (G : Type u) [Group G] {X : Type v} [TopologicalSpace X] [Finite X] [T0Space X]
    [MulAction G X] [IsPretransitive G X]
    (hcts : ∀ g : G, Continuous (fun x : X => g • x)) : DiscreteTopology X := by
  let : R0Space X := r0Space_of_compactSpace_of_isPretransitive G hcts
  let : T1Space X := (t1Space_iff_t0Space_and_r0Space).2 ⟨inferInstance, inferInstance⟩
  infer_instance

private theorem continuous_orbitEquivQuotientStabilizer_symm
    (G : Type u) [Group G] [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [MulAction G X] (x : X)
    (hx : Continuous (fun g : G => g • x)) :
    Continuous (orbitEquivQuotientStabilizer G x).symm := by
  have h : Continuous (ofQuotientStabilizer G x) :=
    ((QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff
      (g := ofQuotientStabilizer G x)).mpr hx
  exact h.subtype_mk (ofQuotientStabilizer_mem_orbit G x)

/-- The canonical orbit–stabilizer homeomorphism for a discrete orbit. -/
noncomputable def orbitHomeomorphQuotientStabilizer
    (G : Type u) [Group G] [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [MulAction G X]
    (x : X) [DiscreteTopology (orbit G x)]
    (hx : Continuous (fun g : G => g • x)) :
    orbit G x ≃ₜ G ⧸ stabilizer G x where
  toEquiv := MulAction.orbitEquivQuotientStabilizer G x
  continuous_toFun := by
    let : DiscreteTopology (G ⧸ stabilizer G x) :=
      DiscreteTopology.of_continuous_injective
        (continuous_orbitEquivQuotientStabilizer_symm G x hx)
        (orbitEquivQuotientStabilizer G x).symm.injective
    exact (orbitEquivQuotientStabilizer G x).toHomeomorphOfDiscrete.continuous_toFun
  continuous_invFun := by exact continuous_orbitEquivQuotientStabilizer_symm G x hx

variable (G : Type u) [Group G] [TopologicalSpace G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X]
variable (x : X) [DiscreteTopology (orbit G x)]
variable (hx : Continuous (fun g : G => g • x))

/-- The underlying equivalence is the canonical orbit–stabilizer equivalence. -/
theorem orbitHomeomorphQuotientStabilizer_toEquiv :
    (orbitHomeomorphQuotientStabilizer G x hx).toEquiv =
      orbitEquivQuotientStabilizer G x := by rfl

/-- The inverse sends the left coset of `g` to the orbit point `g • x`. -/
theorem orbitHomeomorphQuotientStabilizer_symm_mk_coe (g : G) :
    ((orbitHomeomorphQuotientStabilizer G x hx).symm
      (QuotientGroup.mk g) : X) = g • x := by rfl

/-- The orbit point represented by `g` maps to the left coset of `g`. -/
theorem orbitHomeomorphQuotientStabilizer_apply_smul (g : G) :
    orbitHomeomorphQuotientStabilizer G x hx ⟨g • x, ⟨g, rfl⟩⟩ =
      (QuotientGroup.mk g : G ⧸ stabilizer G x) := by
  let e := orbitEquivQuotientStabilizer G x
  have hy : e.symm (QuotientGroup.mk g) =
      (⟨g • x, ⟨g, rfl⟩⟩ : orbit G x) :=
    Subtype.ext (orbitHomeomorphQuotientStabilizer_symm_mk_coe G x hx g)
  exact (congrArg e hy.symm).trans (e.right_inv _)

/-- The homeomorphism commutes with the canonical action on the orbit. -/
theorem orbitHomeomorphQuotientStabilizer_smul (g : G) (y : orbit G x) :
    orbitHomeomorphQuotientStabilizer G x hx (g • y) =
      g • orbitHomeomorphQuotientStabilizer G x hx y := by
  exact orbitEquivQuotientStabilizer_smul x g y

/-- The inverse homeomorphism commutes with the canonical quotient action. -/
theorem orbitHomeomorphQuotientStabilizer_symm_smul (g : G)
    (q : G ⧸ stabilizer G x) :
    (orbitHomeomorphQuotientStabilizer G x hx).symm (g • q) =
      g • (orbitHomeomorphQuotientStabilizer G x hx).symm q := by
  exact orbitEquivQuotientStabilizer_symm_smul x g q

end MulAction

namespace MulActionHom

/-- Continuity of the orbit map at `f x` follows from continuity at `x`
when the source orbit is discrete. -/
theorem continuous_smul_map
    {G : Type u} [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [SMul G X]
    {Y : Type w} [TopologicalSpace Y] [SMul G Y]
    (f : X →[G] Y) (x : X) [DiscreteTopology (MulAction.orbit G x)]
    (hx : Continuous (fun g : G => g • x)) :
    Continuous (fun g : G => g • f x) := by
  have hOrbit : Continuous (fun g : G =>
      (⟨g • x, ⟨g, rfl⟩⟩ : MulAction.orbit G x)) :=
    hx.subtype_mk (fun g => ⟨g, rfl⟩)
  have hf : Continuous (fun z : MulAction.orbit G x => f (z : X)) :=
    continuous_of_discreteTopology
  have hfx : Continuous (fun g : G => f (g • x)) := hf.comp hOrbit
  simpa only [f.map_smul] using hfx

/-- The orbit–stabilizer homeomorphisms commute with equivariant maps and the
quotient maps induced by stabilizer inclusions. -/
theorem orbitHomeomorphQuotientStabilizer_naturality
    {G : Type u} [Group G] [TopologicalSpace G]
    {X : Type v} [TopologicalSpace X] [MulAction G X]
    {Y : Type w} [TopologicalSpace Y] [MulAction G Y]
    (f : X →[G] Y) (x : X)
    [DiscreteTopology (MulAction.orbit G x)]
    [DiscreteTopology (MulAction.orbit G (f x))]
    (hx : Continuous (fun g : G => g • x)) (z : MulAction.orbit G x) :
    MulAction.orbitHomeomorphQuotientStabilizer G (f x)
        (f.continuous_smul_map x hx) (f.orbitMap x z) =
      MulActionHom.quotientMapOfLE (f.stabilizer_le x)
        (MulAction.orbitHomeomorphQuotientStabilizer G x hx z) := by
  exact f.orbitEquivQuotientStabilizer_naturality x z

end MulActionHom
