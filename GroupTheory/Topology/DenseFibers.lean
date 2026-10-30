/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Separation.Basic
public import GroupTheory.Topology.QuotientGroup

/-!
# Maps with dense fibers

A map whose every fiber is dense is surjective on a nonempty space. Its preimages
are dense exactly for nonempty sets, and open exactly for the empty and whole sets.
Consequently its coinduced topology is indiscrete. Every such map is open for any
topology on its target. With a nontrivial T1 target, it is continuous at no point.
-/

@[expose] public section

open Set Filter Topology

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α] {f : α → β}

/-- A map with dense fibers on a nonempty space is surjective. -/
theorem surjective_of_dense_fibers [Nonempty α]
    (hd : ∀ b, Dense (f ⁻¹' {b})) : Function.Surjective f := by
  intro b
  obtain ⟨a, ha⟩ := (hd b).nonempty
  exact ⟨a, ha⟩

/-- For a map with dense fibers, a preimage is dense exactly when its set is nonempty. -/
theorem dense_preimage_iff_of_dense_fibers [Nonempty α]
    (hd : ∀ b, Dense (f ⁻¹' {b})) {s : Set β} :
    Dense (f ⁻¹' s) ↔ s.Nonempty := by
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := hs.nonempty
    exact ⟨f a, ha⟩
  · rintro ⟨b, hb⟩
    apply (hd b).mono
    intro a ha
    change f a ∈ s
    change f a = b at ha
    simpa only [ha] using hb

/-- Every nonempty open set maps onto the target of a map with dense fibers. -/
theorem image_eq_univ_of_dense_fibers (hd : ∀ b, Dense (f ⁻¹' {b}))
    {s : Set α} (hs : IsOpen s) (hne : s.Nonempty) : f '' s = univ := by
  apply eq_univ_of_forall
  intro b
  obtain ⟨a, hab, has⟩ := (hd b).exists_mem_open hs hne
  exact ⟨a, has, hab⟩

/-- A map with dense fibers is open for every topology on its target. -/
theorem isOpenMap_of_dense_fibers [TopologicalSpace β]
    (hd : ∀ b, Dense (f ⁻¹' {b})) : IsOpenMap f := by
  intro s hs
  by_cases hne : s.Nonempty
  · rw [image_eq_univ_of_dense_fibers hd hs hne]
    exact isOpen_univ
  · rw [not_nonempty_iff_eq_empty.mp hne, image_empty]
    exact isOpen_empty

/-- A surjection with dense fibers coinduces the indiscrete topology. -/
theorem Function.Surjective.coinduced_eq_top_of_dense_fibers
    (hf : Function.Surjective f) (hd : ∀ b, Dense (f ⁻¹' {b})) :
    TopologicalSpace.coinduced f ‹TopologicalSpace α› = ⊤ := by
  have hopen : @IsOpenMap α β ‹TopologicalSpace α›
      (TopologicalSpace.coinduced f ‹TopologicalSpace α›) f :=
    @isOpenMap_of_dense_fibers α β ‹TopologicalSpace α› f
      (TopologicalSpace.coinduced f ‹TopologicalSpace α›) hd
  have hcont : @Continuous α β ‹TopologicalSpace α›
      (TopologicalSpace.coinduced f ‹TopologicalSpace α›) f := continuous_coinduced_rng
  exact (@IsOpenMap.topology_eq_top_iff_dense_fibers α β ‹TopologicalSpace α›
    (TopologicalSpace.coinduced f ‹TopologicalSpace α›) f hopen hcont hf).2 hd

/-- The topology coinduced by a map with dense fibers on a nonempty space is indiscrete. -/
theorem coinduced_eq_top_of_dense_fibers [Nonempty α]
    (hd : ∀ b, Dense (f ⁻¹' {b})) :
    TopologicalSpace.coinduced f ‹TopologicalSpace α› = ⊤ :=
  (surjective_of_dense_fibers hd).coinduced_eq_top_of_dense_fibers hd

/-- Only the empty and whole sets have open preimages under a surjection with dense fibers. -/
theorem Function.Surjective.isOpen_preimage_iff_of_dense_fibers
    (hf : Function.Surjective f) (hd : ∀ b, Dense (f ⁻¹' {b})) {s : Set β} :
    IsOpen (f ⁻¹' s) ↔ s = ∅ ∨ s = univ := by
  change IsOpen[TopologicalSpace.coinduced f ‹TopologicalSpace α›] s ↔ _
  rw [hf.coinduced_eq_top_of_dense_fibers hd]
  exact TopologicalSpace.isOpen_top_iff s

/-- For a map with dense fibers, only the empty and whole sets have open preimages. -/
theorem isOpen_preimage_iff_of_dense_fibers [Nonempty α]
    (hd : ∀ b, Dense (f ⁻¹' {b})) {s : Set β} :
    IsOpen (f ⁻¹' s) ↔ s = ∅ ∨ s = univ :=
  (surjective_of_dense_fibers hd).isOpen_preimage_iff_of_dense_fibers hd

/-- A map with dense fibers into a nontrivial T1 space is continuous at no point. -/
theorem not_continuousAt_of_dense_fibers [TopologicalSpace β] [T1Space β] [Nontrivial β]
    (hd : ∀ b, Dense (f ⁻¹' {b})) (a : α) : ¬ ContinuousAt f a := by
  intro hc
  obtain ⟨b, hb⟩ := exists_ne (f a)
  have hnb : f ⁻¹' ({b}ᶜ) ∈ 𝓝 a :=
    hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by simpa using hb.symm))
  obtain ⟨x, hxnb, hxb⟩ := mem_closure_iff_nhds.mp (hd b a) _ hnb
  exact hxnb hxb
