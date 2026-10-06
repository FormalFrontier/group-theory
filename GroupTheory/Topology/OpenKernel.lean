/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CompactOpenSubgroup
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Open kernels and finite images

A continuous homomorphism out of a nonarchimedean group has open kernel when an identity
neighborhood in the target contains no nontrivial subgroup. Compactness of the source
then gives finite image and a finite quotient by the kernel. Neither the source's
commutativity nor the target's Hausdorffness is required for these statements.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  remarks following Theorem (1.1.11), for the compact totally disconnected character case.
* Mathlib's `NonarchimedeanGroup`, `QuotientGroup.kerLift`, and
  `IsLocallyConstant.range_finite` supply the general group-theoretic interfaces.

The open-kernel statement applies more generally than the compact groups considered
in the cited remarks. Finite image requires the separate compactness hypothesis.
For example, the identity on discrete `ℤ` has open kernel and infinite image.
The identity on `Circle` has a compact source and subgroup-free target neighborhood,
but its kernel is not open: the source lacks an open-subgroup identity basis.
The identity on a nondiscrete profinite group likewise shows why a subgroup-free
target neighborhood is needed. The trivial source satisfies all conclusions.
-/

@[expose] public section

open Filter
open scoped Topology Pointwise

universe u v

namespace NonarchimedeanGroup

/-- A totally disconnected locally compact topological group has an open-subgroup
neighborhood basis. No separate Hausdorff hypothesis is needed. -/
theorem of_locallyCompact_totallyDisconnected (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨H, _, hH⟩ := OpenSubgroup.exists_compact_subset_nhds_one hU
    exact ⟨H, hH⟩

end NonarchimedeanGroup

namespace MonoidHom

variable {G : Type u} {K : Type v} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [Group K]

/-- An open kernel makes all fibers of a group homomorphism open. Neither
continuity nor a topology on the target is needed for this implication. -/
@[to_additive]
theorem isLocallyConstant_of_isOpen_ker (f : G →* K)
    (hker : IsOpen (f.ker : Set G)) : IsLocallyConstant (f : G → K) := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro x
  have hfiber : (f : G → K) ⁻¹' {f x} = x • (f.ker : Set G) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    exact f.eq_iff
  rw [hfiber]
  exact hker.leftCoset x

end MonoidHom

namespace ContinuousMonoidHom

variable {G : Type u} {K : Type v} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [Group K] [TopologicalSpace K]

/-- A continuous homomorphism from a group with an open-subgroup identity basis
has open kernel if a target identity neighborhood contains no nontrivial subgroup. -/
@[to_additive]
theorem isOpen_ker_of_subgroup_free_nhds (f : G →ₜ* K) (V : Set K)
    (hV : V ∈ 𝓝 (1 : K))
    (hVsub : ∀ H : Subgroup K, (H : Set K) ⊆ V → H = ⊥) :
    IsOpen (f.toMonoidHom.ker : Set G) := by
  have hpre : f ⁻¹' V ∈ 𝓝 (1 : G) := by
    have hcont : Continuous (f : G → K) := f.continuous_toFun
    simpa only [Filter.mem_map] using
      ((hcont.tendsto (1 : G)) (by simpa using hV))
  obtain ⟨U, hUV⟩ := NonarchimedeanGroup.is_nonarchimedean _ hpre
  have hmap : U.toSubgroup.map f.toMonoidHom = ⊥ :=
    hVsub _ (by
      rintro y ⟨x, hx, rfl⟩
      exact hUV hx)
  refine Subgroup.isOpen_of_openSubgroup f.toMonoidHom.ker (U := U) ?_
  intro x hx
  have hfx : f.toMonoidHom x ∈ U.toSubgroup.map f.toMonoidHom := ⟨x, hx, rfl⟩
  simpa only [hmap, Subgroup.mem_bot, MonoidHom.mem_ker] using hfx

/-- Compactness upgrades the open kernel to a finite image; no discrete topology
is imposed on the target. -/
@[to_additive]
theorem finite_range_of_subgroup_free_nhds [CompactSpace G] (f : G →ₜ* K)
    (V : Set K) (hV : V ∈ 𝓝 (1 : K))
    (hVsub : ∀ H : Subgroup K, (H : Set K) ⊆ V → H = ⊥) :
    (Set.range f).Finite := by
  exact (f.toMonoidHom.isLocallyConstant_of_isOpen_ker
    (f.isOpen_ker_of_subgroup_free_nhds V hV hVsub)).range_finite

/-- The quotient by the kernel is finite and discrete. Mathlib's canonical
`QuotientGroup.kerLift` is exactly the unique homomorphism through which `f`
factors. Its injectivity is `QuotientGroup.kerLift_injective`; its codomain
need not equal the image of `f`. Mathlib's `QuotientGroup.quotientKerEquivRange`
identifies this quotient with the image instead. -/
@[to_additive]
theorem finite_quotient_kerLift [CompactSpace G] (f : G →ₜ* K)
    (V : Set K) (hV : V ∈ 𝓝 (1 : K))
    (hVsub : ∀ H : Subgroup K, (H : Set K) ⊆ V → H = ⊥) :
    Finite (G ⧸ f.toMonoidHom.ker) ∧
      DiscreteTopology (G ⧸ f.toMonoidHom.ker) ∧
      (QuotientGroup.kerLift f.toMonoidHom).comp
        (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom ∧
      ∀ lift : G ⧸ f.toMonoidHom.ker →* K,
        lift.comp (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom →
          lift = QuotientGroup.kerLift f.toMonoidHom := by
  have hopen := f.isOpen_ker_of_subgroup_free_nhds V hV hVsub
  have htriangle : (QuotientGroup.kerLift f.toMonoidHom).comp
      (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom := by
    ext x
    exact QuotientGroup.kerLift_mk f.toMonoidHom x
  refine ⟨Subgroup.quotient_finite_of_isOpen _ hopen,
    QuotientGroup.discreteTopology hopen, htriangle, ?_⟩
  intro lift hlift
  exact QuotientGroup.monoidHom_ext f.toMonoidHom.ker (hlift.trans htriangle.symm)

end ContinuousMonoidHom

end
