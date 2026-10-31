/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Sets.Closeds
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Order.WellFounded

/-!
# Closed self-embeddings and irreducible components

A closed self-embedding is surjective if the space has finitely many irreducible
components and strict inclusion of nonempty irreducible closed subsets is
well-founded. The space need not be Noetherian or satisfy a separation axiom.

The proof first cancels a closed embedding on an invariant irreducible closed
subset. It then uses the periodic points of a chosen map on the finite family of
components; this map is not assumed to be injective.
-/

@[expose] public section

open Set Function

universe v

namespace Topology.IsClosedEmbedding

variable {X : Type v} [TopologicalSpace X] {f : X → X}

private theorem image_eq_of_image_subset
    [WellFoundedLT (TopologicalSpace.IrreducibleCloseds X)]
    (hf : Topology.IsClosedEmbedding f) (C : TopologicalSpace.IrreducibleCloseds X)
    (hC : f '' (C : Set X) ⊆ C) : f '' (C : Set X) = C := by
  revert hC
  induction C using (wellFounded_lt (α := TopologicalSpace.IrreducibleCloseds X)).induction
  rename_i C ih
  intro hC
  let D : TopologicalSpace.IrreducibleCloseds X :=
    ⟨f '' (C : Set X), C.isIrreducible.image f hf.continuous.continuousOn,
      hf.isClosedMap _ C.isClosed⟩
  have hDC : D ≤ C := hC
  by_cases hEq : D = C
  · exact congrArg (fun E : TopologicalSpace.IrreducibleCloseds X => (E : Set X)) hEq
  · have hlt : D < C := lt_of_le_of_ne hDC hEq
    have hD : f '' (D : Set X) = D := ih D hlt (Set.image_mono hC)
    exact (Set.image_eq_image hf.injective).mp hD

/-- A closed self-embedding of a space with finitely many irreducible components
is surjective if strict inclusion of nonempty irreducible closed subsets is
well-founded. This includes the empty space and requires no separation axiom. -/
theorem surjective_of_finite_irreducibleComponents
    (hf : Topology.IsClosedEmbedding f) (hfin : (irreducibleComponents X).Finite)
    [WellFoundedLT (TopologicalSpace.IrreducibleCloseds X)] : Function.Surjective f := by
  classical
  let C := {I : Set X // I ∈ irreducibleComponents X}
  let : Fintype C := hfin.fintype
  have hex (I : C) : ∃ J : C, f '' (I : Set X) ⊆ (J : Set X) := by
    obtain ⟨J, hJ, hIJ⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible
        (f '' (I : Set X)) (I.property.1.image f hf.continuous.continuousOn)
    exact ⟨⟨J, hJ⟩, hIJ⟩
  let F : C → C := fun I => Classical.choose (hex I)
  have hF (I : C) : f '' (I : Set X) ⊆ (F I : Set X) :=
    Classical.choose_spec (hex I)
  have hemb : ∀ n : ℕ, Topology.IsClosedEmbedding (f^[n]) := by
    intro n
    induction n with
    | zero => simpa only [Function.iterate_zero] using
        (Topology.IsClosedEmbedding.id : Topology.IsClosedEmbedding (@id X))
    | succ n ih =>
      rw [Function.iterate_succ]
      exact ih.comp hf
  have hcontain : ∀ n (I : C), (f^[n]) '' (I : Set X) ⊆ (F^[n] I : Set X) := by
    intro n
    induction n with
    | zero => intro I; simp
    | succ n ih =>
      intro I
      calc
        (f^[n + 1]) '' (I : Set X) = (f^[n]) '' (f '' (I : Set X)) := by
          simp only [Function.iterate_succ, Set.image_image, Function.comp_def]
        _ ⊆ (f^[n]) '' (F I : Set X) := Set.image_mono (hF I)
        _ ⊆ (F^[n] (F I) : Set X) := ih (F I)
        _ = (F^[n + 1] I : Set X) := by rw [Function.iterate_succ_apply]
  -- A positive component cycle has exact, rather than merely contained, images.
  have hper_image (I : C) (hI : I ∈ Function.periodicPts F) :
      f '' (I : Set X) = (F I : Set X) := by
    obtain ⟨p, hp, hpI⟩ := Function.mem_periodicPts.mp hI
    cases p with
    | zero => exact (Nat.lt_irrefl 0 hp).elim
    | succ p =>
      have hpEq : F^[p + 1] I = I := hpI
      have hsub : (f^[p + 1]) '' (I : Set X) ⊆ (I : Set X) := by
        simpa only [hpEq] using hcontain (p + 1) I
      have hfix : (f^[p + 1]) '' (I : Set X) = (I : Set X) :=
        image_eq_of_image_subset (hemb (p + 1))
          ⟨(I : Set X), I.property.1,
            isClosed_of_mem_irreducibleComponents _ I.property⟩ hsub
      have hpStep : F^[p] (F I) = I := by
        simpa only [Function.iterate_succ_apply] using hpEq
      apply Set.Subset.antisymm (hF I)
      intro y hy
      have hFy : f^[p] y ∈ (I : Set X) := by
        have h := hcontain p (F I) (Set.mem_image_of_mem _ hy)
        simpa only [hpStep] using h
      have hyImage : f^[p] y ∈ (f^[p + 1]) '' (I : Set X) := by
        rw [hfix]
        exact hFy
      obtain ⟨x, hx, hxy⟩ := hyImage
      refine ⟨x, hx, (hf.injective.iterate p) ?_⟩
      simpa only [Function.iterate_succ_apply] using hxy
  have hper_iterate : ∀ n (I : C), I ∈ Function.periodicPts F →
      (f^[n]) '' (I : Set X) = (F^[n] I : Set X) := by
    intro n
    induction n with
    | zero => intro I _; simp
    | succ n ih =>
      intro I hI
      have hFI : F I ∈ Function.periodicPts F :=
        (Function.bijOn_periodicPts F).mapsTo hI
      calc
        (f^[n + 1]) '' (I : Set X) = (f^[n]) '' (f '' (I : Set X)) := by
          simp only [Function.iterate_succ, Set.image_image, Function.comp_def]
        _ = (f^[n]) '' (F I : Set X) := by rw [hper_image I hI]
        _ = (F^[n] (F I) : Set X) := ih (F I) hFI
        _ = (F^[n + 1] I : Set X) := by rw [Function.iterate_succ_apply]
  -- Finiteness gives an eventual positive cycle, not injectivity of F.
  have hper_all (I : C) : I ∈ Function.periodicPts F := by
    have hrep : ∃ m n : ℕ, m < n ∧ F^[m] I = F^[n] I := by
      obtain ⟨m, n, hmn, heq⟩ :=
        Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F^[n] I)
      rcases lt_or_gt_of_ne hmn with h | h
      · exact ⟨m, n, h, heq⟩
      · exact ⟨n, m, h, heq.symm⟩
    obtain ⟨m, n, hmn, heq⟩ := hrep
    have hJ : F^[m] I ∈ Function.periodicPts F := by
      refine Function.mem_periodicPts.mpr ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
      change F^[n - m] (F^[m] I) = F^[m] I
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hmn)]
      exact heq.symm
    obtain ⟨K, hK, hKJ⟩ := (Function.bijOn_periodicPts F).surjOn.iterate m hJ
    have hIK : (I : Set X) ⊆ (K : Set X) := by
      apply (Set.image_subset_image_iff (hf.injective.iterate m)).mp
      rw [hper_iterate m K hK, hKJ]
      exact hcontain m I
    have hEq : I = K :=
      Subtype.ext (Set.Subset.antisymm hIK (I.property.2 K.property.1 hIK))
    exact hEq.symm ▸ hK
  intro y
  let I : C :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  obtain ⟨J, hJ, hJI⟩ := (Function.bijOn_periodicPts F).surjOn (hper_all I)
  have hy : y ∈ f '' (J : Set X) := by
    rw [hper_image J hJ, hJI]
    exact mem_irreducibleComponent
  obtain ⟨x, _, hxy⟩ := hy
  exact ⟨x, hxy⟩

end Topology.IsClosedEmbedding
