/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import GroupTheory.Topology.Algebra.MonoidHom.CompactPowerControl

/-!
# Compact families of continuous monoid homomorphisms

The forgetful map to functions with uniform convergence on every compact set is inducing for
the compact-open topology. Its image need not be closed for an arbitrary source. Nevertheless,
a closed equicontinuous family of continuous monoid homomorphisms has closed image: pointwise
closure preserves equicontinuity, so every limit in that image closure is continuous, and the
homomorphism equations are closed when the target is Hausdorff.

Combining this family-local closedness with Mathlib's general Arzelà–Ascoli theorem gives a
compactness criterion for homomorphisms from any topologized monoid to a Hausdorff topological
group. The criterion is stated using left differences and the original compact-open topology;
the compatible left uniformity is used only inside its proof.

## References

The proof uses the Arzelà–Ascoli framework in `Mathlib.Topology.UniformSpace.Ascoli`, together
with Mathlib's compact-convergence comparison and preservation of equicontinuity under
pointwise closure. The continuous-limit and closed-homomorphism arguments below provide the
family-local bridge to the compact-open homomorphism space.

For a source topological group, a common bound on an identity neighborhood in a compact
subgroup-free set supplies the required equicontinuity. The resulting compactness criterion
combines the left-difference criterion with algebraic compact power control.
-/

@[expose] public section

open Filter Set Topology

universe u v

namespace ContinuousMonoidHom

/-- The compact-open topology on continuous monoid homomorphisms is induced by uniform
convergence on all compact subsets, with no local compactness assumption on the source. -/
theorem isInducing_toUniformOnFunIsCompact
    {M : Type u} {D : Type v}
    [Monoid M] [TopologicalSpace M] [Monoid D] [UniformSpace D] :
    IsInducing (fun f : M →ₜ* D => f.toContinuousMap.toUniformOnFunIsCompact) := by
  exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding.isInducing.comp
    (isInducing_toContinuousMap M D)

/-- A closed equicontinuous family has closed image in the space of all functions with
uniform convergence on compact subsets. Only this family, not the entire continuous-map
space, is asserted to have closed image. Pointwise bounds are not required. -/
theorem isClosed_range_toUniformOnFunIsCompact_of_isClosed_of_equicontinuous
    {M : Type u} {D : Type v}
    [Monoid M] [TopologicalSpace M] [Monoid D] [UniformSpace D]
    [ContinuousMul D] [T2Space D]
    (K : Set (M →ₜ* D)) (hK : IsClosed K)
    (hequi : Equicontinuous (fun f : K => (f.val : M → D))) :
    IsClosed (range (fun f : K => f.val.toContinuousMap.toUniformOnFunIsCompact)) := by
  classical
  let 𝔖 : Set (Set M) := {s | IsCompact s}
  let U := UniformOnFun M D 𝔖
  let F : K → U := fun f => f.val.toContinuousMap.toUniformOnFunIsCompact
  let A : Set U := range F
  have heval (x : M) : Continuous (fun g : U => UniformOnFun.toFun 𝔖 g x) := by
    exact (UniformOnFun.uniformContinuous_eval_of_mem
      (β := D) (𝔖 := 𝔖) (s := {x}) (x := x) (by simp) isCompact_singleton).continuous
  have hpointwise : Continuous (UniformOnFun.toFun 𝔖 : U → M → D) :=
    continuous_pi heval
  let r : A → K := fun a => Classical.choose a.property
  have hreindex : (UniformOnFun.toFun 𝔖 ∘ ((↑) : A → U)) =
      (fun f : K => (f.val : M → D)) ∘ r := by
    funext a
    exact congrArg (UniformOnFun.toFun 𝔖) (Classical.choose_spec a.property).symm
  have hA : Equicontinuous (UniformOnFun.toFun 𝔖 ∘ ((↑) : A → U)) := by
    rw [hreindex]
    exact hequi.comp r
  have hclosure : Equicontinuous
      (UniformOnFun.toFun 𝔖 ∘ ((↑) : closure A → U)) :=
    hA.closure' hpointwise
  have hone : closure A ⊆ {g : U | UniformOnFun.toFun 𝔖 g 1 = 1} := by
    apply closure_minimal
    · rintro _ ⟨f, rfl⟩
      exact map_one f.val
    · exact isClosed_eq (heval 1) continuous_const
  have hmul (x y : M) : closure A ⊆
      {g : U | UniformOnFun.toFun 𝔖 g (x * y) =
        UniformOnFun.toFun 𝔖 g x * UniformOnFun.toFun 𝔖 g y} := by
    apply closure_minimal
    · rintro _ ⟨f, rfl⟩
      exact map_mul f.val x y
    · exact isClosed_eq (heval (x * y)) ((heval x).mul (heval y))
  have himage : (fun f : M →ₜ* D => f.toContinuousMap.toUniformOnFunIsCompact) '' K = A := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
  change IsClosed A
  have hsubset : closure A ⊆ A := by
    intro g hg
    have hgcont : Continuous (UniformOnFun.toFun 𝔖 g) := hclosure.continuous ⟨g, hg⟩
    let f : M →ₜ* D :=
      { toFun := UniformOnFun.toFun 𝔖 g
        map_one' := hone hg
        map_mul' := fun x y => hmul x y hg
        continuous_toFun := hgcont }
    have hfg : f.toContinuousMap.toUniformOnFunIsCompact = g := by
      rfl
    have hfclosure : f ∈ closure K := by
      rw [isInducing_toUniformOnFunIsCompact.closure_eq_preimage_closure_image K]
      change f.toContinuousMap.toUniformOnFunIsCompact ∈
        closure ((fun f : M →ₜ* D => f.toContinuousMap.toUniformOnFunIsCompact) '' K)
      rw [himage, hfg]
      exact hg
    have hfK : f ∈ K := by
      rwa [hK.closure_eq] at hfclosure
    exact ⟨⟨f, hfK⟩, hfg⟩
  have hclosure_eq : closure A = A := le_antisymm hsubset subset_closure
  rw [← hclosure_eq]
  exact isClosed_closure

/-- Arzelà–Ascoli for a closed family of continuous monoid homomorphisms, expressed using
left differences in the target. The common neighborhood is independent of the homomorphism,
and each point has a compact set bounding all values of the family. Neither continuity of
the source operations nor local compactness or separation of the source is required.

This is an application of Mathlib's general Arzelà–Ascoli theorem to the compatible left
uniformity, using the family-local closed-image theorem above. -/
theorem isCompact_of_isClosed_of_leftEquicontinuous
    {M : Type u} {D : Type v}
    [Monoid M] [TopologicalSpace M]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [T2Space D]
    (K : Set (M →ₜ* D))
    (hK : IsClosed K)
    (hequi : ∀ x : M, ∀ W : Set D, W ∈ nhds (1 : D) →
      ∃ V : Set M, V ∈ nhds x ∧
        ∀ f ∈ K, ∀ y ∈ V, (f x)⁻¹ * f y ∈ W)
    (hpoint : ∀ x : M, ∃ Q : Set D,
      IsCompact Q ∧ ∀ f ∈ K, f x ∈ Q) :
    IsCompact K := by
  let _ : UniformSpace D := IsTopologicalGroup.leftUniformSpace (G := D)
  have hleft : uniformity D =
      Filter.comap (fun p : D × D => p.1⁻¹ * p.2) (nhds (1 : D)) := by
    rfl
  have hb : (uniformity D).HasBasis (fun W : Set D => W ∈ nhds (1 : D))
      (fun W => {p : D × D | p.1⁻¹ * p.2 ∈ W}) := by
    rw [hleft]
    exact (nhds (1 : D)).basis_sets.comap _
  have hequi' : Equicontinuous (fun f : K => (f.val : M → D)) := by
    intro x
    rw [hb.equicontinuousAt_iff_right]
    intro W hW
    obtain ⟨V, hV, hbound⟩ := hequi x W hW
    filter_upwards [hV] with y hy
    intro f
    exact hbound f.val f.property y hy
  let 𝔖 : Set (Set M) := {s | IsCompact s}
  have hind : IsInducing
      (UniformOnFun.ofFun 𝔖 ∘ (fun f : K => (f.val : M → D))) :=
    isInducing_toUniformOnFunIsCompact.comp IsInducing.subtypeVal
  have hclosed : IsClosed
      (range (UniformOnFun.ofFun 𝔖 ∘ (fun f : K => (f.val : M → D)))) :=
    isClosed_range_toUniformOnFunIsCompact_of_isClosed_of_equicontinuous K hK hequi'
  let _ : CompactSpace K := ArzelaAscoli.compactSpace_of_closed_inducing'
    (fun s hs => hs) hind hclosed
    (fun s _ => hequi'.equicontinuousOn s)
    (by
      intro _ _ x _
      obtain ⟨Q, hQ, hbound⟩ := hpoint x
      exact ⟨Q, hQ, fun f => hbound f.val f.property⟩)
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- A closed family of continuous homomorphisms is compact if it has compact point
containers and sends one common identity neighborhood into a compact set containing no
nontrivial subgroup. No local compactness or global no-small-subgroups hypothesis is needed.

Compact power control supplies common identity control; source translation then gives the
left differences required by `isCompact_of_isClosed_of_leftEquicontinuous`. -/
theorem isCompact_of_isClosed_of_mapsTo
    {G : Type u} {D : Type v}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [T2Space D]
    (S : Set (G →ₜ* D)) (hS : IsClosed S)
    {Q : Set G} (hQ : Q ∈ nhds (1 : G))
    {K : Set D} (hK : IsCompact K)
    (hK_subgroup : ∀ H : Subgroup D, (H : Set D) ⊆ K → H = ⊥)
    (hSK : ∀ f ∈ S, Set.MapsTo f Q K)
    (hpoint : ∀ x : G, ∃ P : Set D, IsCompact P ∧ ∀ f ∈ S, f x ∈ P) :
    IsCompact S := by
  have hcontrol : ∀ W : Set D, W ∈ nhds (1 : D) →
      ∃ U : Set G, U ∈ nhds (1 : G) ∧ ∀ f ∈ S, MapsTo f U W := by
    intro W hW
    let A : Set (G →* D) :=
      (fun f : G →ₜ* D => f.toMonoidHom) '' S
    have hAbound : ∀ f ∈ A, MapsTo f Q K := by
      rintro f ⟨g, hg, rfl⟩
      exact hSK g hg
    obtain ⟨U, hUnhds, hUbound⟩ :=
      MonoidHom.exists_nhds_one_forall_mapsTo
        hQ hK hK.isClosed hK_subgroup hAbound hW
    refine ⟨U, hUnhds, ?_⟩
    intro f hf
    exact hUbound f.toMonoidHom ⟨f, hf, rfl⟩
  have hleft : ∀ x : G, ∀ W : Set D, W ∈ nhds (1 : D) →
      ∃ V : Set G, V ∈ nhds x ∧
        ∀ f ∈ S, ∀ y ∈ V, (f x)⁻¹ * f y ∈ W := by
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
  exact isCompact_of_isClosed_of_leftEquicontinuous S hS hleft hpoint

end ContinuousMonoidHom
