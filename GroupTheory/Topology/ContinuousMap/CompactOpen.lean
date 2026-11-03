/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Separation.Regular

/-!
# Joint postcomposition in the compact-open topology

An embedding into a product induces an embedding of continuous-map spaces by its two
postcomposition maps if either the source or the original target is R1. No local
compactness or separation assumption on the two coordinate targets is needed.

The proof uses closed neighborhoods in a compact R1 space: either the fixed compact
source subset or its image in the original target. The resulting closed pieces are
pulled back to the compact source subset before being included in the source. No compact
subset is asserted to be closed in an ambient space. The compact-open topology and its
bundled continuous maps are those of Mathlib.
-/

@[expose] public section

open Set Filter Topology

universe u v w z

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

private theorem exists_open_rectangle (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) {U : Set Y} (hU : IsOpen U)
    {y : Y} (hy : y ∈ U) :
    ∃ V : Set Z, ∃ T : Set W, IsOpen V ∧ IsOpen T ∧ j₁ y ∈ V ∧ j₂ y ∈ T ∧
      j₁ ⁻¹' V ∩ j₂ ⁻¹' T ⊆ U := by
  have hUy : U ∈ comap (fun y => (j₁ y, j₂ y)) (𝓝 (j₁ y, j₂ y)) := by
    rw [← hj.isInducing.nhds_eq_comap]
    exact hU.mem_nhds hy
  obtain ⟨O, hO, hOU⟩ := mem_comap.mp hUy
  rw [nhds_prod_eq] at hO
  obtain ⟨V, hV, T, hT, hVT⟩ := mem_prod_iff.mp hO
  obtain ⟨V', hV'V, hV', hyV'⟩ := mem_nhds_iff.mp hV
  obtain ⟨T', hT'T, hT', hyT'⟩ := mem_nhds_iff.mp hT
  refine ⟨V', T', hV', hT', hyV', hyT', ?_⟩
  intro q hq
  exact hOU (hVT ⟨hV'V hq.1, hT'T hq.2⟩)

private theorem exists_open_postcomp_prod {A : Type*} [TopologicalSpace A]
    [CompactSpace A] [R1Space A] (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) (h₀ : C(X, Y))
    {K : Set X} (hK : IsCompact K) {U : Set Y} (hU : IsOpen U)
    (p : K → A) (hp : Continuous p) (q : C(A, Y))
    (hpq : ∀ x : K, q (p x) = h₀ x) (hqU : ∀ a, q a ∈ U) :
    ∃ N : Set (C(X, Z) × C(X, W)), IsOpen N ∧ (j₁.comp h₀, j₂.comp h₀) ∈ N ∧
      (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) ⁻¹' N ⊆
        {h | MapsTo h K U} := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose V T hV hT hpV hpT hVT using
    fun a : A => exists_open_rectangle j₁ j₂ hj hU (hqU a)
  let O : A → Set A := fun a =>
    {b | j₁ (q b) ∈ V a ∧ j₂ (q b) ∈ T a}
  have hO (a : A) : IsOpen (O a) :=
    ((hV a).preimage (j₁.continuous.comp q.continuous)).inter
      ((hT a).preimage (j₂.continuous.comp q.continuous))
  have hpO (a : A) : a ∈ O a := ⟨hpV a, hpT a⟩
  -- Compact R1 spaces are regular; the following closures are taken in A.
  have hRefine (a : A) :
      ∃ B : Set A, (a ∈ B ∧ IsOpen B) ∧ closure B ⊆ O a :=
    (hasBasis_opens_closure a).mem_iff.mp ((hO a).mem_nhds (hpO a))
  let B : A → Set A := fun a => Classical.choose (hRefine a)
  have hpB (a : A) : a ∈ B a := (Classical.choose_spec (hRefine a)).1.1
  have hB (a : A) : IsOpen (B a) := (Classical.choose_spec (hRefine a)).1.2
  have hBc (a : A) : closure (B a) ⊆ O a :=
    (Classical.choose_spec (hRefine a)).2
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover B hB (by
    intro a _
    exact mem_iUnion.mpr ⟨a, hpB a⟩)
  let L : A → Set X := fun a => Subtype.val '' (p ⁻¹' closure (B a))
  have hL (a : A) : IsCompact (L a) :=
    ((isClosed_closure.preimage hp).isCompact).image continuous_subtype_val
  let N₁ : Set C(X, Z) := ⋂ a : s, {f | MapsTo f (L a.1) (V a.1)}
  let N₂ : Set C(X, W) := ⋂ a : s, {f | MapsTo f (L a.1) (T a.1)}
  have hN₁ : IsOpen N₁ :=
    isOpen_iInter_of_finite fun a => isOpen_setOfPred_mapsTo (hL a.1) (hV a.1)
  have hN₂ : IsOpen N₂ :=
    isOpen_iInter_of_finite fun a => isOpen_setOfPred_mapsTo (hL a.1) (hT a.1)
  refine ⟨N₁ ×ˢ N₂, hN₁.prod hN₂, ?_, ?_⟩
  · constructor
    · apply mem_iInter.mpr
      intro a x hx
      obtain ⟨b, hb, rfl⟩ := hx
      change j₁ (h₀ b) ∈ V a.1
      rw [← hpq b]
      exact (hBc a.1 hb).1
    · apply mem_iInter.mpr
      intro a x hx
      obtain ⟨b, hb, rfl⟩ := hx
      change j₂ (h₀ b) ∈ T a.1
      rw [← hpq b]
      exact (hBc a.1 hb).2
  · intro h hh x hx
    have hxA : p ⟨x, hx⟩ ∈ (univ : Set A) := mem_univ _
    obtain ⟨a, has, ha⟩ := mem_iUnion₂.mp (hs hxA)
    have hxL : x ∈ L a := ⟨⟨x, hx⟩, subset_closure ha, rfl⟩
    exact hVT a ⟨(mem_iInter.mp hh.1 ⟨a, has⟩) hxL,
      (mem_iInter.mp hh.2 ⟨a, has⟩) hxL⟩

private theorem isEmbedding_postcomp_prod_of_neighborhoods
    (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y))
    (hN : ∀ (h₀ : C(X, Y)) (K : Set X) (U : Set Y), IsCompact K → IsOpen U →
      MapsTo h₀ K U →
      ∃ N : Set (C(X, Z) × C(X, W)), IsOpen N ∧ (j₁.comp h₀, j₂.comp h₀) ∈ N ∧
        (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) ⁻¹' N ⊆
          {h | MapsTo h K U}) :
    IsEmbedding (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) := by
  classical
  let J : C(X, Y) → C(X, Z) × C(X, W) := fun h => (j₁.comp h, j₂.comp h)
  have hJ : Continuous J :=
    (continuous_postcomp j₁).prodMk (continuous_postcomp j₂)
  have hJinj : Function.Injective J := by
    intro f g hfg
    ext x
    apply hj.injective
    exact congrArg (fun p : C(X, Z) × C(X, W) => (p.1 x, p.2 x)) hfg
  let e : C(X, Y) ≃ Set.range J := Equiv.ofInjective J hJinj
  have heq (p : Set.range J) :
      (j₁.comp (e.symm p), j₂.comp (e.symm p)) = p.1 :=
    congrArg Subtype.val (e.apply_symm_apply p)
  have he : Continuous e := hJ.subtype_mk _
  have heInv : Continuous e.symm := by
    apply continuous_generateFrom_iff.mpr
    intro S hS
    suffices ∀ (K : Set X) (U : Set Y), IsCompact K → IsOpen U →
        IsOpen (e.symm ⁻¹' {h | MapsTo h K U}) by
      aesop
    intro K U hK hU
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨N, hNopen, hpN, hNsub⟩ := hN (e.symm p) K U hK hU hp
    have hpN' : p ∈ Subtype.val ⁻¹' N := by
      simpa only [Set.mem_preimage, ← heq p] using hpN
    apply mem_of_superset ((hNopen.preimage continuous_subtype_val).mem_nhds hpN')
    intro q hq
    apply hNsub
    simpa only [Set.mem_preimage, heq q] using hq
  let e' : C(X, Y) ≃ₜ Set.range J :=
    { e with continuous_toFun := he, continuous_invFun := heInv }
  change IsEmbedding (Subtype.val ∘ e')
  exact Topology.IsEmbedding.subtypeVal.comp e'.isEmbedding

/-- Joint postcomposition with the coordinates of an embedding is an embedding for the
compact-open topologies when the original target is R1. The source and the two coordinate
targets need not satisfy any separation or local compactness assumption. -/
theorem isEmbedding_postcomp_prod [R1Space Y] (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) :
    IsEmbedding (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) := by
  apply isEmbedding_postcomp_prod_of_neighborhoods j₁ j₂ hj
  intro h₀ K U hK hU h₀KU
  let F : Set Y := h₀ '' K
  let : CompactSpace F := isCompact_iff_compactSpace.mp (hK.image h₀.continuous)
  let r : K → F := fun x => ⟨h₀ x, ⟨x, x.property, rfl⟩⟩
  have hr : Continuous r :=
    (h₀.continuous.comp continuous_subtype_val).subtype_mk _
  apply exists_open_postcomp_prod j₁ j₂ hj h₀ hK hU r hr
    (⟨Subtype.val, continuous_subtype_val⟩ : C(F, Y)) (fun _ => rfl)
  rintro ⟨_, x, hx, rfl⟩
  exact h₀KU hx

/-- Joint postcomposition with the coordinates of an embedding is an embedding for the
compact-open topologies when the source is R1. No separation assumption on the original
target or the two coordinate targets, or local compactness assumption, is needed. -/
theorem isEmbedding_postcomp_prod_of_r1Space_domain [R1Space X]
    (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) :
    IsEmbedding (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) := by
  apply isEmbedding_postcomp_prod_of_neighborhoods j₁ j₂ hj
  intro h₀ K U hK hU h₀KU
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact exists_open_postcomp_prod j₁ j₂ hj h₀ hK hU id continuous_id
    (⟨fun x : K => h₀ x, h₀.continuous.comp continuous_subtype_val⟩ : C(K, Y))
    (fun _ => rfl) (fun x => h₀KU x.property)

end ContinuousMap
