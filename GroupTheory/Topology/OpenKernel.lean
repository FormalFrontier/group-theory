/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CompactOpenSubgroup
public import GroupTheory.Topology.FiniteIndex
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Open kernels and finite images

A continuous homomorphism out of a nonarchimedean group has open kernel when an identity
neighborhood in the target contains no nontrivial subgroup. Compactness of the source
then gives finite image and a finite quotient by the kernel. Neither the source's
commutativity nor the target's Hausdorffness is required for these statements.

For a compact Hausdorff commutative source with a dense finitely generated subgroup,
an abstract homomorphism with finite range is locally constant even when its target
only has a multiplication with identity (`MulOneClass`). This uses finite-index
openness and requires no target topology; local constancy gives continuity for any
subsequently given target topology. The additive target only needs `AddZeroClass`.

For monoid targets, one fixed positive natural exponent annihilating every image
element is another sufficient condition for open kernel and local constancy.
This uses the open power-range theorem, with no target topology or continuity
assumed. Its additive counterpart has an additive monoid target.

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

section OpenKernel

variable {G : Type u} {K : Type v} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [MulOneClass K]

/-- An open kernel makes a homomorphism out of a group locally constant. The target
only needs a multiplication with identity: neither target inverses, associativity,
continuity nor a topology on the target is needed. -/
@[to_additive /-- An open kernel makes a homomorphism out of an additive group locally
constant. The target only needs an addition with zero: neither target negation,
associativity, continuity nor a topology on the target is needed. -/]
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

end OpenKernel

section FiniteRange

variable {A : Type u} {M : Type v} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [MulOneClass M]

/-- An abstract homomorphism with finite range from a compact Hausdorff commutative
group with a dense finitely generated subgroup is locally constant. The target only
needs a multiplication with identity and no topology. The proof uses finite-index
openness for the kernel. -/
@[to_additive /-- An abstract additive homomorphism with finite range from a compact Hausdorff
  commutative additive group with a dense finitely generated subgroup is locally constant.
  The target only needs an addition with zero and no topology. The proof uses finite-index
  openness for the kernel. -/]
theorem isLocallyConstant_of_dense_fg_of_finite_range (f : A →* M) (D : Subgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A)) (hf : (Set.range f).Finite) :
    IsLocallyConstant (f : A → M) := by
  have hrel : ∀ x y, QuotientGroup.leftRel f.ker x y ↔ Setoid.ker (f : A → M) x y := by
    intro x y
    rw [QuotientGroup.leftRel_apply, ← f.eq_iff, Setoid.ker_def]
    exact eq_comm
  let e : A ⧸ f.ker ≃ Set.range (f : A → M) :=
    (Quotient.congrRight hrel).trans (Setoid.quotientKerEquivRange (f : A → M))
  let : Finite (Set.range (f : A → M)) := hf.to_subtype
  let : Finite (A ⧸ f.ker) := Finite.of_equiv _ e.symm
  let : f.ker.FiniteIndex := Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  have hopen := Subgroup.isOpen_of_finiteIndex_of_dense_fg D hfg hdense f.ker
  exact f.isLocallyConstant_of_isOpen_ker hopen

end FiniteRange

section BoundedExponent

variable {G : Type u} {M : Type v} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [Monoid M]

/-- An abstract homomorphism from a compact Hausdorff commutative group with a dense
finitely generated subgroup has open kernel if one positive exponent annihilates its
whole image. No topology on the target or continuity of the homomorphism is assumed. -/
@[to_additive /-- An abstract additive homomorphism from a compact Hausdorff commutative additive
  group with a dense finitely generated subgroup has open kernel if one positive natural
  scalar annihilates its whole image. No topology on the target or continuity is assumed. -/]
theorem isOpen_ker_of_dense_fg_of_pow_eq_one (f : G →* M) (D : Subgroup G)
    (hfg : D.FG) (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ x, (f x) ^ n = 1) : IsOpen (f.ker : Set G) := by
  apply Subgroup.isOpen_mono (H₁ := (powMonoidHom (α := G) n).range)
    (H₂ := f.ker) ?_ (Subgroup.isOpen_range_powMonoidHom_of_dense_fg D hfg hdense hn)
  rintro _ ⟨x, rfl⟩
  exact (map_pow f x n).trans (hpow x)

/-- An abstract homomorphism from a compact Hausdorff commutative group with a dense
finitely generated subgroup is locally constant if one positive exponent annihilates
its whole image. The target is an arbitrary monoid with no topology specified. -/
@[to_additive /-- An abstract additive homomorphism from a compact Hausdorff commutative additive
  group with a dense finitely generated subgroup is locally constant if one positive
  natural scalar annihilates its whole image. No topology on the target is specified. -/]
theorem isLocallyConstant_of_dense_fg_of_pow_eq_one (f : G →* M) (D : Subgroup G)
    (hfg : D.FG) (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ x, (f x) ^ n = 1) : IsLocallyConstant (f : G → M) :=
  f.isLocallyConstant_of_isOpen_ker
    (f.isOpen_ker_of_dense_fg_of_pow_eq_one D hfg hdense hn hpow)

end BoundedExponent

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
