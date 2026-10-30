/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex
public import GroupTheoryTest.Topology.PadicDenseIntegers
import GroupTheory.Topology.OpenKernel
import GroupTheory.Topology.Ultrafilter
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Ring.Units
import GroupTheory.Topology.Algebra.Group.TotalBounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod

/-!
# Dense finite generation and open finite-index subgroups

The embedded integers generate a dense additive subgroup of the compact 2-adic
integers. Reduction modulo two gives a proper finite-index subgroup; the open
subgroup result applies without supplying a closedness hypothesis. This example
does not assume that the whole additive group of 2-adic integers is abstractly
finitely generated.

Finite set range makes the kernel of an abstract homomorphism finite-index even
when the target only has a multiplication with identity. The units inclusion into
`ZMod 3` gives a nonconstant example with a nongroup target.

The powers of `(3)` in the stock 3-adic integers give an independent example of
the finite-index neighborhood-basis criterion for total boundedness. Their
neighborhood-basis and finite-index inputs use norm estimates and algebraic
reduction maps, respectively.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.FiniteIndex

open GroupTheoryTest.Topology.PadicDenseIntegers

universe u v

section FiniteRange

variable {A : Type u} {M : Type v} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [MulOneClass M]
  (D : Subgroup A) (hfg : D.FG) (hdense : Dense (D : Set A))
  (f : A →* M) (hf : (Set.range f).Finite)

include hfg hdense hf

example [TopologicalSpace M] : Continuous (f : A → M) :=
  (f.isLocallyConstant_of_dense_fg_of_finite_range D hfg hdense hf).continuous

end FiniteRange

-- The units topology is discrete; the target multiplication has a nonunit zero.
example :
    let f := Units.coeHom (ZMod 3)
    IsOpen (f ⁻¹' {1}) ∧ IsLocallyConstant f ∧ Continuous f ∧
      (f ⁻¹' {1}).Nonempty ∧ f ⁻¹' {1} ≠ Set.univ ∧
      f 1 ≠ f (-1) ∧ ¬ ∃ z : ZMod 3, 0 * z = 1 := by
  let f := Units.coeHom (ZMod 3)
  let : Finite (ZMod 3)ˣ :=
    Finite.of_injective (Units.val : (ZMod 3)ˣ → ZMod 3) Units.val_injective
  have hfg : (⊤ : Subgroup (ZMod 3)ˣ).FG :=
    (Group.fg_iff_subgroup_fg _).mp inferInstance
  have hdense : Dense ((⊤ : Subgroup (ZMod 3)ˣ) : Set (ZMod 3)ˣ) := by simp
  have hlc := f.isLocallyConstant_of_dense_fg_of_finite_range
    ⊤ hfg hdense (Set.toFinite _)
  have hopen : IsOpen (f ⁻¹' {1}) := by
    simpa only [f.map_one] using
      (IsLocallyConstant.iff_isOpen_fiber_apply.mp hlc (1 : (ZMod 3)ˣ))
  have hfiber : f ⁻¹' {1} = ({1} : Set (ZMod 3)ˣ) := by
    ext x
    change f x = 1 ↔ x = 1
    rw [← f.map_one]
    exact (Units.coeHom_injective (M := ZMod 3)).eq_iff
  have hneg : f (-1) = 2 := by
    norm_num [f, Units.coeHom_apply]
    decide
  have hne : f 1 ≠ f (-1) := by
    rw [f.map_one, hneg]
    decide
  refine ⟨hopen, hlc, hlc.continuous, ⟨1, f.map_one⟩, ?_, hne, ?_⟩
  · intro h
    have hmem : (-1 : (ZMod 3)ˣ) ∈ f ⁻¹' {1} := by
      rw [h]
      trivial
    have heq : (-1 : (ZMod 3)ˣ) = 1 := by
      simpa only [hfiber, Set.mem_singleton_iff] using hmem
    exact hne (congrArg f heq.symm)
  · simp

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private noncomputable def parityKernel : AddSubgroup ℤ_[2] :=
  (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom.ker

/-- Doubling in the 2-adic integers has finite-index open image, witnessed by a
dense copy of the finitely generated additive group of integers. -/
theorem two_nsmul_range_finiteIndex_and_open :
    (nsmulAddMonoidHom (α := ℤ_[2]) 2).range.FiniteIndex ∧
      IsOpen ((nsmulAddMonoidHom (α := ℤ_[2]) 2).range : Set ℤ_[2]) := by
  exact ⟨AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_dense_fg
    padicIntegers padicIntegers_fg padicIntegers_dense (by norm_num),
    AddSubgroup.isOpen_range_nsmulAddMonoidHom_of_dense_fg
      padicIntegers padicIntegers_fg padicIntegers_dense (by norm_num)⟩

/-- The 2-adic integers have a proper open additive subgroup given by reduction modulo two. -/
private theorem parityKernel_open_and_proper : IsOpen (parityKernel : Set ℤ_[2]) ∧
    parityKernel ≠ ⊤ := by
  have hsurj : Function.Surjective (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) :=
    ZMod.ringHom_surjective _
  have hfinite : parityKernel.FiniteIndex := by
    dsimp [parityKernel]
    infer_instance
  constructor
  · exact @AddSubgroup.isOpen_of_finiteIndex_of_dense_fg ℤ_[2] _ _ _ _ _
      padicIntegers padicIntegers_fg padicIntegers_dense parityKernel hfinite
  · intro htop
    obtain ⟨element, helement⟩ := hsurj (1 : ZMod 2)
    have hmem : element ∈ parityKernel := by rw [htop]; exact AddSubgroup.mem_top _
    have hzero : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) element = 0 := by
      change ((PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom element) = 0 at hmem
      exact hmem
    exact one_ne_zero (helement.symm.trans hzero)

/-- The positivity assumption on the exponent cannot be removed for the infinite
compact group of 2-adic integers: the zero scalar map has infinite index. -/
theorem zero_nsmul_range_not_finiteIndex :
    ¬ (nsmulAddMonoidHom (α := ℤ_[2]) 0).range.FiniteIndex := by
  have hrange : (nsmulAddMonoidHom (α := ℤ_[2]) 0).range =
      (⊥ : AddSubgroup ℤ_[2]) := by
    ext element
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, zero_nsmul,
      exists_const, AddSubgroup.mem_bot]
    exact eq_comm
  rw [hrange, AddSubgroup.not_finiteIndex_iff, AddSubgroup.index_bot,
    Nat.card_eq_zero_of_infinite]

/-- In the discrete integers, the zero-subgroup neighborhood basis fails finite
index, so the additive criterion rules out total boundedness. -/
private theorem int_not_totallyBounded : ¬ TotallyBounded (Set.univ : Set ℤ) := by
  have hBasis :
      (nhds (0 : ℤ)).HasBasis (fun _ : Unit => True)
        (fun _ => ((⊥ : AddSubgroup ℤ) : Set ℤ)) := by
    simpa only [nhds_discrete ℤ, AddSubgroup.coe_bot] using
      (Filter.hasBasis_pure (0 : ℤ))
  have hindex : ¬ (⊥ : AddSubgroup ℤ).FiniteIndex := by
    rw [AddSubgroup.not_finiteIndex_iff, AddSubgroup.index_bot,
      Nat.card_eq_zero_of_infinite]
  intro htotallyBounded
  exact hindex
    ((hBasis.totallyBounded_univ_iff_addSubgroup_finiteIndex.mp htotallyBounded) () trivial)

/-! The powers of `(3)` in the stock normed ring of 3-adic integers provide a
non-discrete subgroup basis. Its finite-index inputs come from reduction modulo
`3 ^ n`, independently of compactness. -/

private theorem padicThree_closedBall_eq_power (n : ℕ) :
    Metric.closedBall (0 : ℤ_[3]) ((1 / 3 : ℝ) ^ n) =
      (((Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n).toAddSubgroup : Set ℤ_[3]) := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (1 / 3 : ℝ) ^ n ↔ x ∈ (Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n
  rw [Ideal.span_singleton_pow]
  simpa only [Nat.cast_ofNat, zpow_neg, zpow_natCast, one_div, inv_pow] using
    (PadicInt.norm_le_pow_iff_mem_span_pow x n)

private theorem padicThree_power_basis :
    (nhds (0 : ℤ_[3])).HasBasis (fun _ : ℕ => True)
      (fun n => (((Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n).toAddSubgroup :
        Set ℤ_[3])) := by
  exact (Metric.nhds_basis_closedBall_pow (x := (0 : ℤ_[3]))
    (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).congr
      (fun _ => Iff.rfl) (fun n _ => padicThree_closedBall_eq_power n)

private theorem padicThree_power_finiteIndex (n : ℕ) :
    ((Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n).toAddSubgroup.FiniteIndex := by
  have hker : ((Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n).toAddSubgroup =
      (PadicInt.toZModPow n : ℤ_[3] →+* ZMod (3 ^ n)).toAddMonoidHom.ker := by
    ext x
    change x ∈ (Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n ↔
      (PadicInt.toZModPow n : ℤ_[3] →+* ZMod (3 ^ n)) x = 0
    rw [Ideal.span_singleton_pow]
    have hker' := PadicInt.ker_toZModPow (p := 3) n
    simp only [Nat.cast_ofNat] at hker'
    rw [← hker', RingHom.mem_ker]
  rw [hker]
  exact AddSubgroup.finiteIndex_ker _

private theorem padicThree_totallyBounded : TotallyBounded (Set.univ : Set ℤ_[3]) := by
  exact padicThree_power_basis.totallyBounded_univ_iff_addSubgroup_finiteIndex.mpr
    (fun n _ => padicThree_power_finiteIndex n)

private theorem padicThree_multiplicative_power_basis :
    (nhds (1 : Multiplicative ℤ_[3])).HasBasis (fun _ : ℕ => True)
      (fun n =>
        (((Ideal.span {(3 : ℤ_[3])} : Ideal ℤ_[3]) ^ n).toAddSubgroup.toSubgroup :
          Set (Multiplicative ℤ_[3]))) := by
  rw [← ofAdd_zero, nhds_ofAdd]
  refine (padicThree_power_basis.map Multiplicative.ofAdd).congr (fun _ => Iff.rfl) ?_
  intro n _
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Multiplicative.mem_toSubgroup _ _).mpr ha
  · intro hx
    exact ⟨x.toAdd, (Multiplicative.mem_toSubgroup _ _).mp hx, ofAdd_toAdd x⟩

private theorem padicThree_multiplicative_totallyBounded :
    TotallyBounded (Set.univ : Set (Multiplicative ℤ_[3])) := by
  exact padicThree_multiplicative_power_basis.totallyBounded_univ_iff_subgroup_finiteIndex.mpr
    (fun n _ => (AddSubgroup.finiteIndex_toSubgroup_iff _).mpr
      (padicThree_power_finiteIndex n))

end GroupTheoryTest.Topology.FiniteIndex

end

section

open Topology

universe u v

example {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) [H.FiniteIndex] (hH : IsClosed (H : Set G)) :
    (H : Set G) ∈ 𝓝 (1 : G) :=
  H.isOpen_iff_mem_nhds_one.mp (H.isOpen_iff_isClosed.mpr hH)

example {A : Type v} [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    (H : AddSubgroup A) [H.FiniteIndex] (hH : IsClosed (H : Set A)) :
    (H : Set A) ∈ 𝓝 (0 : A) :=
  H.isOpen_iff_mem_nhds_zero.mp (H.isOpen_iff_isClosed.mpr hH)

example {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) : IsClopen (H : Set G) ↔ IsOpen (H : Set G) :=
  H.isClopen_iff_isOpen

example {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) [H.FiniteIndex] : IsOpen (H : Set G) ↔ IsClosed (H : Set G) :=
  H.isOpen_iff_isClosed

example {A : Type v} [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    (K : AddSubgroup A) : IsClopen (K : Set A) ↔ IsOpen (K : Set A) :=
  K.isClopen_iff_isOpen

example {A : Type v} [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    (K : AddSubgroup A) [K.FiniteIndex] : IsOpen (K : Set A) ↔ IsClosed (K : Set A) :=
  K.isOpen_iff_isClosed

end

/-!
## Finite-index pullbacks along ultrafilter limits

For an ultrafilter finer than the cofinite filter, pulling back a proper
finite-index subgroup along its limit homomorphism gives a finite-index subgroup
that is not open. The same obstruction applies to additive groups and, for a
finite nontrivial T1 target, to the kernel of the prescribed limit homomorphism.
-/

section UltrafilterPullbacks

universe u v

example {ι : Type u} {G : Type v} [Group G] [TopologicalSpace G]
    [CompactSpace G] [T2Space G] [ContinuousMul G]
    (U : Ultrafilter ι) (hU : (U : Filter ι) ≤ Filter.cofinite)
    (H : Subgroup G) [H.FiniteIndex] (hH : H ≠ ⊤) :
    (H.comap (U.limMonoidHom)).FiniteIndex ∧
      ¬ IsOpen (H.comap (U.limMonoidHom) : Set (ι → G)) := by
  constructor
  · have hrel : H.IsFiniteRelIndex (⊤ : Subgroup G) :=
      Subgroup.isFiniteRelIndex_top_iff.mpr inferInstance
    have hcomap : (H.comap U.limMonoidHom).IsFiniteRelIndex
        (⊤ : Subgroup (ι → G)) := by
      simpa using
        (Subgroup.IsFiniteRelIndex.comap (H := H) (K := ⊤) U.limMonoidHom hrel)
    exact Subgroup.isFiniteRelIndex_top_iff.mp hcomap
  · intro hopen
    exact hH ((Ultrafilter.isOpen_comap_limMonoidHom_iff U hU H).mp hopen)

example {ι : Type u} {A : Type v} [AddGroup A] [TopologicalSpace A]
    [CompactSpace A] [T2Space A] [ContinuousAdd A]
    (U : Ultrafilter ι) (hU : (U : Filter ι) ≤ Filter.cofinite)
    (H : AddSubgroup A) [H.FiniteIndex] (hH : H ≠ ⊤) :
    (H.comap (U.limAddMonoidHom)).FiniteIndex ∧
      ¬ IsOpen (H.comap (U.limAddMonoidHom) : Set (ι → A)) := by
  constructor
  · have hrel : H.IsFiniteRelIndex (⊤ : AddSubgroup A) :=
      AddSubgroup.isFiniteRelIndex_top_iff.mpr inferInstance
    have hcomap : (H.comap U.limAddMonoidHom).IsFiniteRelIndex
        (⊤ : AddSubgroup (ι → A)) := by
      simpa using
        (AddSubgroup.IsFiniteRelIndex.comap (H := H) (K := ⊤) U.limAddMonoidHom hrel)
    exact AddSubgroup.isFiniteRelIndex_top_iff.mp hcomap
  · intro hopen
    exact hH ((Ultrafilter.isOpen_comap_limAddMonoidHom_iff U hU H).mp hopen)

example {ι : Type u} {G : Type v} [Group G] [Finite G]
    [TopologicalSpace G] [T1Space G] [Nontrivial G]
    (U : Ultrafilter ι) (hU : (U : Filter ι) ≤ Filter.cofinite) :
    (U.limMonoidHom : (ι → G) →* G).ker.FiniteIndex ∧
      ¬ IsOpen ((U.limMonoidHom : (ι → G) →* G).ker : Set (ι → G)) := by
  constructor
  · infer_instance
  · intro hopen
    have hbot : (⊥ : Subgroup G) = ⊤ :=
      (Ultrafilter.isOpen_comap_limMonoidHom_iff U hU (⊥ : Subgroup G)).mp
        (by simpa using hopen)
    exact bot_ne_top hbot

end UltrafilterPullbacks
