/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex
public import GroupTheoryTest.Topology.PadicDenseIntegers
import Mathlib.Algebra.CharZero.Infinite
import GroupTheory.Topology.Algebra.Group.TotalBounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Constructions

/-!
# Dense finite generation and open finite-index subgroups

The embedded integers generate a dense additive subgroup of the compact 2-adic
integers. Reduction modulo two gives a proper finite-index subgroup; the open
subgroup result applies without supplying a closedness hypothesis. This example
does not assume that the whole additive group of 2-adic integers is abstractly
finitely generated.

The powers of `(3)` in the stock 3-adic integers give an independent example of
the finite-index neighborhood-basis criterion for total boundedness. Their
neighborhood-basis and finite-index inputs use norm estimates and algebraic
reduction maps, respectively.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.FiniteIndex

open GroupTheoryTest.Topology.PadicDenseIntegers

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
