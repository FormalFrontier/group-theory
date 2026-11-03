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
postcomposition maps, provided the original target is R1. No local compactness or
separation assumption on the source is needed.

The proof uses closed neighborhoods in the compact image of a fixed compact set. In
particular, this image is not asserted to be closed in the ambient target. The
compact-open topology and its bundled continuous maps are those of Mathlib.
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

private theorem exists_open_postcomp_prod [R1Space Y]
    (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) (h₀ : C(X, Y))
    {K : Set X} (hK : IsCompact K) {U : Set Y} (hU : IsOpen U)
    (h₀KU : MapsTo h₀ K U) :
    ∃ N : Set (C(X, Z) × C(X, W)), IsOpen N ∧ (j₁.comp h₀, j₂.comp h₀) ∈ N ∧
      (fun h : C(X, Y) => (j₁.comp h, j₂.comp h)) ⁻¹' N ⊆
        {h | MapsTo h K U} := by
  classical
  let F : Set Y := h₀ '' K
  let : CompactSpace F := isCompact_iff_compactSpace.mp (hK.image h₀.continuous)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hFU : F ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact h₀KU hx
  choose V T hV hT hpV hpT hVT using
    fun p : F => exists_open_rectangle j₁ j₂ hj hU (hFU p.property)
  let O : F → Set F := fun p =>
    {q | j₁ q.1 ∈ V p ∧ j₂ q.1 ∈ T p}
  have hO (p : F) : IsOpen (O p) :=
    ((hV p).preimage (j₁.continuous.comp continuous_subtype_val)).inter
      ((hT p).preimage (j₂.continuous.comp continuous_subtype_val))
  have hpO (p : F) : p ∈ O p := ⟨hpV p, hpT p⟩
  -- Compact R1 spaces are regular; all the following closures are taken in F.
  have hRefine (p : F) :
      ∃ A : Set F, (p ∈ A ∧ IsOpen A) ∧ closure A ⊆ O p :=
    (hasBasis_opens_closure p).mem_iff.mp ((hO p).mem_nhds (hpO p))
  let A : F → Set F := fun p => Classical.choose (hRefine p)
  have hpA (p : F) : p ∈ A p := (Classical.choose_spec (hRefine p)).1.1
  have hA (p : F) : IsOpen (A p) := (Classical.choose_spec (hRefine p)).1.2
  have hAc (p : F) : closure (A p) ⊆ O p :=
    (Classical.choose_spec (hRefine p)).2
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover A hA (by
    intro p _
    exact mem_iUnion.mpr ⟨p, hpA p⟩)
  let r : K → F := fun x => ⟨h₀ x, ⟨x, x.property, rfl⟩⟩
  have hr : Continuous r :=
    (h₀.continuous.comp continuous_subtype_val).subtype_mk _
  let L : F → Set X := fun p => Subtype.val '' (r ⁻¹' closure (A p))
  have hL (p : F) : IsCompact (L p) :=
    ((isClosed_closure.preimage hr).isCompact).image continuous_subtype_val
  let N₁ : Set C(X, Z) := ⋂ p : s, {f | MapsTo f (L p.1) (V p.1)}
  let N₂ : Set C(X, W) := ⋂ p : s, {f | MapsTo f (L p.1) (T p.1)}
  have hN₁ : IsOpen N₁ :=
    isOpen_iInter_of_finite fun p => isOpen_setOfPred_mapsTo (hL p.1) (hV p.1)
  have hN₂ : IsOpen N₂ :=
    isOpen_iInter_of_finite fun p => isOpen_setOfPred_mapsTo (hL p.1) (hT p.1)
  refine ⟨N₁ ×ˢ N₂, hN₁.prod hN₂, ?_, ?_⟩
  · constructor
    · apply mem_iInter.mpr
      intro p x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact (hAc p.1 ha).1
    · apply mem_iInter.mpr
      intro p x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact (hAc p.1 ha).2
  · intro h hh x hx
    have hxF : r ⟨x, hx⟩ ∈ (univ : Set F) := mem_univ _
    obtain ⟨p, hps, hp⟩ := mem_iUnion₂.mp (hs hxF)
    have hxL : x ∈ L p := ⟨⟨x, hx⟩, subset_closure hp, rfl⟩
    exact hVT p ⟨(mem_iInter.mp hh.1 ⟨p, hps⟩) hxL,
      (mem_iInter.mp hh.2 ⟨p, hps⟩) hxL⟩

/-- Joint postcomposition with the coordinates of an embedding is an embedding for the
compact-open topologies when the original target is R1. The source and the two coordinate
targets need not satisfy any separation or local compactness assumption. -/
theorem isEmbedding_postcomp_prod [R1Space Y] (j₁ : C(Y, Z)) (j₂ : C(Y, W))
    (hj : IsEmbedding fun y => (j₁ y, j₂ y)) :
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
    obtain ⟨N, hN, hpN, hNsub⟩ :=
      exists_open_postcomp_prod j₁ j₂ hj (e.symm p) hK hU hp
    have hpN' : p ∈ Subtype.val ⁻¹' N := by
      simpa only [Set.mem_preimage, ← heq p] using hpN
    apply mem_of_superset ((hN.preimage continuous_subtype_val).mem_nhds hpN')
    intro q hq
    apply hNsub
    simpa only [Set.mem_preimage, heq q] using hq
  let e' : C(X, Y) ≃ₜ Set.range J :=
    { e with continuous_toFun := he, continuous_invFun := heInv }
  change IsEmbedding (Subtype.val ∘ e')
  exact Topology.IsEmbedding.subtypeVal.comp e'.isEmbedding

end ContinuousMap
