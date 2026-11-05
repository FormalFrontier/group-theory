/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.CompactFamilies
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.CompactNeighborhoods
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import GroupTheory.Topology.Algebra.MonoidHom.CompactPowerControl

/-!
# Local compactness of homomorphisms into compact groups with no small subgroups

A common-bound family is a closed neighborhood in the original compact-open topology.
Compact power control supplies common identity control, and source translation gives the
left-difference condition of the compact-family criterion. Compactness of the target supplies
the point bounds. No compact generation or commutativity hypothesis is needed.

## References

The proof combines the compact-neighborhood assembly and the compact-family criterion in the
imported continuous-monoid-hom modules with the compact closed subgroup-free neighborhood
criterion and algebraic compact power control in the imported group and monoid-hom modules.
-/

@[expose] public section

open Set Filter Topology

universe u v

/-- The compact-open space of continuous homomorphisms from a locally compact group into a
compact group with no small subgroups is locally compact. Neither compact generation of the
source nor commutativity of the target is assumed. -/
theorem ContinuousMonoidHom.locallyCompactSpace_of_compactSpace
    {G : Type u} {D : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [NoSmallSubgroups D] :
    LocallyCompactSpace (G →ₜ* D) := by
  let _ : T2Space D := inferInstance
  let _ : T2Space (G →ₜ* D) := inferInstance
  obtain ⟨K, hKnhds, hKcompact, hKclosed, hKfree⟩ :=
    noSmallSubgroups_iff_exists_isCompact_isClosed_nhds_one.mp
      (inferInstance : NoSmallSubgroups D)
  have hcompactNhds : ∀ f₀ : G →ₜ* D,
      ∃ A : Set (G →ₜ* D), IsCompact A ∧ A ∈ nhds f₀ := by
    intro f₀
    obtain ⟨Q, hQnhds, _, P, _, hN⟩ :=
      ContinuousMonoidHom.exists_isCompact_bounds_mem_nhds
        f₀ (∅ : Set G) isCompact_empty K hKnhds
    let A : Set (G →ₜ* D) := {f | MapsTo f Q K}
    have hAnhds : A ∈ nhds f₀ := by
      exact Filter.mem_of_superset hN fun f hf => hf.1
    have heval (x : G) : Continuous (fun f : G →ₜ* D => f x) := by
      apply continuous_def.mpr
      intro V hV
      have hopen : IsOpen {f : C(G, D) | MapsTo f ({x} : Set G) V} :=
        ContinuousMap.isOpen_setOfPred_mapsTo isCompact_singleton hV
      have hpre : (fun f : G →ₜ* D => f x) ⁻¹' V =
          (fun f : G →ₜ* D => f.toContinuousMap) ⁻¹'
            {f : C(G, D) | MapsTo f ({x} : Set G) V} := by
        ext f
        constructor
        · intro hf y hy
          have hyx : y = x := Set.mem_singleton_iff.mp hy
          subst y
          exact hf
        · intro hf
          exact hf (by rfl)
      rw [hpre]
      exact hopen.preimage
        (ContinuousMonoidHom.isInducing_toContinuousMap G D).continuous
    have hAclosed : IsClosed A := by
      have heq : A = ⋂ x : G, ⋂ (_ : x ∈ Q),
          (fun f : G →ₜ* D => f x) ⁻¹' K := by
        ext f
        constructor
        · intro hf
          apply mem_iInter.mpr
          intro x
          apply mem_iInter.mpr
          intro hx
          exact hf hx
        · intro hf x hx
          exact mem_iInter.mp (mem_iInter.mp hf x) hx
      rw [heq]
      exact isClosed_iInter fun x =>
        isClosed_iInter fun _ => hKclosed.preimage (heval x)
    have hcontrol : ∀ W : Set D, W ∈ nhds (1 : D) →
        ∃ U : Set G, U ∈ nhds (1 : G) ∧
          ∀ f ∈ A, MapsTo f U W := by
      intro W hW
      let S : Set (G →* D) :=
        (fun f : G →ₜ* D => f.toMonoidHom) '' A
      have hSbound : ∀ f ∈ S, MapsTo f Q K := by
        rintro f ⟨g, hg, rfl⟩
        exact hg
      obtain ⟨U, hUnhds, hUbound⟩ :=
        MonoidHom.exists_nhds_one_forall_mapsTo
          hQnhds hKcompact hKclosed hKfree hSbound hW
      refine ⟨U, hUnhds, ?_⟩
      intro f hf
      exact hUbound f.toMonoidHom ⟨f, hf, rfl⟩
    have hleft : ∀ x : G, ∀ W : Set D, W ∈ nhds (1 : D) →
        ∃ V : Set G, V ∈ nhds x ∧
          ∀ f ∈ A, ∀ y ∈ V, (f x)⁻¹ * f y ∈ W := by
      intro x W hW
      obtain ⟨U, hUnhds, hUbound⟩ := hcontrol W hW
      have htranslate : Continuous (fun y : G => x⁻¹ * y) :=
        continuous_const.mul continuous_id
      have hUat : U ∈ nhds (x⁻¹ * x) := by
        simpa only [inv_mul_cancel] using hUnhds
      refine ⟨(fun y : G => x⁻¹ * y) ⁻¹' U,
        htranslate.continuousAt.preimage_mem_nhds hUat, ?_⟩
      intro f hf y hy
      have hvalue : f (x⁻¹ * y) ∈ W := hUbound f hf hy
      simpa only [map_mul, map_inv] using hvalue
    have hpoint : ∀ x : G, ∃ B : Set D,
        IsCompact B ∧ ∀ f ∈ A, f x ∈ B := by
      intro x
      exact ⟨univ, isCompact_univ, fun f hf => mem_univ (f x)⟩
    have hAcompact : IsCompact A :=
      ContinuousMonoidHom.isCompact_of_isClosed_of_leftEquicontinuous
        A hAclosed hleft hpoint
    exact ⟨A, hAcompact, hAnhds⟩
  let _ : WeaklyLocallyCompactSpace (G →ₜ* D) := ⟨hcompactNhds⟩
  infer_instance
