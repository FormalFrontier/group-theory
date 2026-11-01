/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.PontryaginDual
public import GroupTheory.Topology.TypeTags
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Real characters and canonical bidual evaluation

The real parameter `r` gives the continuous character
`x ↦ Real.fourierChar (r * x)`. The classification statement specifies that every
continuous character of the additive real line has a unique such parameter.
`PontryaginDual.realEquiv` packages this parametrization as a continuous additive
equivalence onto the entire Pontryagin dual, with its compact-open topology.
`PontryaginDual.realEvalEquiv` has the canonical bidual evaluation as its forward map.

## Implementation notes

The real line and all type tags retain their original topologies. The Fourier
character uses period-one normalization, rather than the radian normalization of
`Circle.exp`. The parameter map uses the existing compact-open type-tag equivalence
and continuity of the jointly continuous Fourier kernel.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.10)–(1.1.11), for the dual-group definition and canonical biduality setting.
  Real character classification and Fourier self-duality here are auxiliary
  real-case results in that setting.
* Mathlib's `Analysis.Complex.Circle` (Heather Macbeth), for `Real.fourierChar`,
  and `Topology.Algebra.Group.CompactOpen` (Thomas Browning and Nailin Guan),
  for the compact-open topology and continuous currying.
* Related lifting and linearization machinery: Mathlib's
  `Analysis.SpecialFunctions.Complex.Circle` and `Topology.Instances.RealVectorSpace`
  (Yury Kudryashov), and `Topology.Homotopy.Lifting` (Junyan Xu).
* Mathlib's `Analysis.Fourier.BoundedContinuousFunctionChar` (Jakob Stiefel),
  for bilinear-character separation, and `Algebra.Algebra.Bilinear`
  (Kenny Lau and Yury Kudryashov), for the multiplication pairing.
-/

@[expose] public section

namespace PontryaginDual

open Filter Set
open scoped Topology

/-- The period-one Fourier family of characters of the additive real line,
with the compact-open topology on the entire character space. -/
noncomputable def realToDual : ℝ →ₜ+ Additive (PontryaginDual (Multiplicative ℝ)) :=
  (ContinuousAddMonoidHom.toContinuousAddMonoidHom
    (ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv.symm :
      (ℝ →ₜ+ Additive Circle) ≃ₜ+ Additive (PontryaginDual (Multiplicative ℝ)))).comp
    { toFun r :=
        { toFun := fun x => Additive.ofMul (Real.fourierChar (r * x))
          map_zero' := by
            change Additive.ofMul (Real.fourierChar (r * 0)) = Additive.ofMul 1
            rw [mul_zero, AddChar.map_zero_eq_one]
          map_add' := by
            intro x y
            change Additive.ofMul (Real.fourierChar (r * (x + y))) =
              Additive.ofMul (Real.fourierChar (r * x) * Real.fourierChar (r * y))
            rw [mul_add, AddChar.map_add_eq_mul]
          continuous_toFun := continuous_ofMul.comp
            (Real.continuous_fourierChar.comp (continuous_const.mul continuous_id)) }
      map_zero' := by
        apply ContinuousAddMonoidHom.ext
        intro x
        change Additive.ofMul (Real.fourierChar (0 * x)) = Additive.ofMul 1
        rw [zero_mul, AddChar.map_zero_eq_one]
      map_add' := by
        intro r s
        apply ContinuousAddMonoidHom.ext
        intro x
        change Additive.ofMul (Real.fourierChar ((r + s) * x)) =
          Additive.ofMul (Real.fourierChar (r * x) * Real.fourierChar (s * x))
        rw [add_mul, AddChar.map_add_eq_mul]
      continuous_toFun := ContinuousAddMonoidHom.continuous_of_continuous_uncurry _
        (continuous_ofMul.comp
          (Real.continuous_fourierChar.comp (continuous_fst.mul continuous_snd))) }

/-- The real parameter map is given by the period-one Fourier kernel. -/
@[simp] theorem realToDual_apply (r x : ℝ) :
    Additive.toMul (realToDual r) (Multiplicative.ofAdd x) =
      Real.fourierChar (r * x) := rfl

private theorem eq_of_fourierChar_mul_eq {r s : ℝ}
    (h : ∀ x : ℝ, Real.fourierChar (r * x) = Real.fourierChar (s * x)) : r = s := by
  refine BoundedContinuousFunction.ext_of_char_eq (L := LinearMap.mul ℝ ℝ)
    Real.continuous_fourierChar Real.fourierChar_ne_one
    (continuous_fst.mul continuous_snd) ?_ ?_
  · intro v hv hzero
    apply hv
    have h1 := congrArg (fun l : ℝ →ₗ[ℝ] ℝ => l 1) hzero
    simpa only [LinearMap.mul_apply', mul_one, LinearMap.zero_apply] using h1
  · intro x
    change (Real.fourierChar (r * x) : ℂ) = (Real.fourierChar (s * x) : ℂ)
    exact congrArg (fun z : Circle => (z : ℂ)) (h x)

/-- Every continuous character of the additive real line has a unique period-one
real frequency. This is an auxiliary real-case classification for Pontryagin duality. -/
theorem existsUnique_real (χ : PontryaginDual (Multiplicative ℝ)) :
    ∃! r : ℝ, ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Real.fourierChar (r * x) := by
  let f : C(ℝ, Circle) :=
    ⟨fun x => χ (Multiplicative.ofAdd x), χ.continuous.comp continuous_ofAdd⟩
  have hf0 : f 0 = 1 := by
    change χ 1 = 1
    exact _root_.map_one χ
  have hfadd (x y : ℝ) : f (x + y) = f x * f y := by
    change χ (Multiplicative.ofAdd x * Multiplicative.ofAdd y) =
      χ (Multiplicative.ofAdd x) * χ (Multiplicative.ofAdd y)
    exact _root_.map_mul χ _ _
  obtain ⟨h, ⟨h0, hlift⟩, hunique⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f (0 : ℝ) (0 : ℝ)
      (by rw [Circle.exp_zero, hf0])
  have hexp (x : ℝ) : Circle.exp (h x) = f x := congrFun hlift x
  -- Translating and rebasing a lift gives another lift based at zero.
  have hadd (x y : ℝ) : h (x + y) = h x + h y := by
    let k : C(ℝ, ℝ) :=
      ⟨fun x => h (x + y) - h y,
        (h.continuous.comp (continuous_id.add continuous_const)).sub continuous_const⟩
    have hk : k 0 = 0 ∧ Circle.exp ∘ k = f := by
      constructor
      · change h (0 + y) - h y = 0
        simp
      · funext x
        change Circle.exp (h (x + y) - h y) = f x
        rw [Circle.exp_sub, hexp, hexp, hfadd]
        simp
    have hk_eq : k = h := hunique k hk
    have hx : h (x + y) - h y = h x := congrArg (fun l : C(ℝ, ℝ) => l x) hk_eq
    exact sub_eq_iff_eq_add.mp hx
  -- Only the real-valued additive lift is real-linearized.
  let g : ℝ →+ ℝ := { toFun := h, map_zero' := h0, map_add' := hadd }
  let L : ℝ →L[ℝ] ℝ := g.toRealLinearMap h.continuous
  have hslope (x : ℝ) : h x = h 1 * x := by
    have hx := L.map_smul x (1 : ℝ)
    change h (x • (1 : ℝ)) = x • h (1 : ℝ) at hx
    simpa only [smul_eq_mul, mul_one, mul_comm] using hx
  -- The exponential lift is in radians, whereas the Fourier character has period one.
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hparam (x : ℝ) : χ (Multiplicative.ofAdd x) =
      Real.fourierChar ((h 1 / (2 * Real.pi)) * x) := by
    calc
      χ (Multiplicative.ofAdd x) = Circle.exp (h x) := (hexp x).symm
      _ = Circle.exp (h 1 * x) := congrArg Circle.exp (hslope x)
      _ = Real.fourierChar ((h 1 / (2 * Real.pi)) * x) := by
        rw [Real.fourierChar_apply']
        congr 1
        rw [← mul_assoc, mul_div_cancel₀ _ hpi]
  refine ⟨h 1 / (2 * Real.pi), hparam, ?_⟩
  intro r hr
  exact eq_of_fourierChar_mul_eq (fun x => (hr x).symm.trans (hparam x))

/-- The Fourier parameter map is bijective onto the entire real Pontryagin dual. -/
theorem realToDual_bijective : Function.Bijective realToDual := by
  constructor
  · intro r s hrs
    obtain ⟨t, _, hunique⟩ := existsUnique_real (Additive.toMul (realToDual r))
    have hr : ∀ x : ℝ, Additive.toMul (realToDual r) (Multiplicative.ofAdd x) =
        Real.fourierChar (r * x) := realToDual_apply r
    have hs : ∀ x : ℝ, Additive.toMul (realToDual r) (Multiplicative.ofAdd x) =
        Real.fourierChar (s * x) := by
      intro x
      rw [hrs, realToDual_apply]
    exact (hunique r hr).trans (hunique s hs).symm
  · intro χ
    obtain ⟨r, hr, _⟩ := existsUnique_real χ.toMul
    refine ⟨r, ?_⟩
    have heq : Additive.toMul (realToDual r) = χ.toMul := by
      apply PontryaginDual.ext
      intro x
      exact (realToDual_apply r x.toAdd).trans (hr x.toAdd).symm
    exact congrArg Additive.ofMul heq

/-- Fourier self-duality of the real line, with its original topology and the
compact-open character topology, using period-one frequencies. This is an auxiliary
real-case result for Pontryagin duality. -/
noncomputable def realEquiv : ℝ ≃ₜ+ Additive (PontryaginDual (Multiplicative ℝ)) where
  toAddEquiv := AddEquiv.ofBijective realToDual realToDual_bijective
  continuous_toFun := realToDual.continuous
  continuous_invFun := by
    -- Only the algebraic inverse is used here: continuity of `realEquiv` is not yet available.
    let e := AddEquiv.ofBijective realToDual realToDual_bijective
    change Continuous e.symm
    apply continuous_of_tendsto_nhds_zero e.symm
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := DFunLike.ne_iff.mp Real.fourierChar_ne_one
    have ht : Real.fourierChar t ≠ 1 := by
      simpa only [AddChar.one_apply] using ht
    let T : Additive (PontryaginDual (Multiplicative ℝ)) ≃ₜ+
        (ℝ →ₜ+ Additive Circle) :=
      ContinuousMonoidHom.toAdditiveRightContinuousAddEquiv
    let K : Set ℝ := Icc (-(|t| / ε)) (|t| / ε)
    let U : Set (Additive Circle) := {Additive.ofMul (Real.fourierChar t)}ᶜ
    let V : Set (Additive (PontryaginDual (Multiplicative ℝ))) :=
      {χ | MapsTo (T χ) K U}
    have hK : IsCompact K := isCompact_Icc
    have hU : IsOpen U := isClosed_singleton.isOpen_compl
    have hV : IsOpen V :=
      (ContinuousMap.isOpen_setOfPred_mapsTo hK hU).preimage
        ((ContinuousAddMonoidHom.isInducing_toContinuousMap ℝ (Additive Circle)).continuous.comp
          T.continuous)
    have hzero : (0 : Additive (PontryaginDual (Multiplicative ℝ))) ∈ V := by
      intro _ _
      change (1 : Circle) ≠ Real.fourierChar t
      exact ht.symm
    filter_upwards [hV.mem_nhds hzero] with χ hχ
    let r : ℝ := e.symm χ
    have hr : realToDual r = χ := e.apply_symm_apply χ
    have habs : |r| < ε := by
      by_contra h
      have hεr : ε ≤ |r| := le_of_not_gt h
      have hr0 : r ≠ 0 := by
        intro h0
        exact (not_le_of_gt hε) (by simpa only [h0, abs_zero] using hεr)
      -- Control on the whole fixed compact interval, not just finitely many evaluations.
      have hx : t / r ∈ K := by
        apply abs_le.mp
        rw [abs_div]
        exact div_le_div_of_nonneg_left (abs_nonneg t) hε hεr
      have hnot : T χ (t / r) ≠ Additive.ofMul (Real.fourierChar t) := hχ hx
      apply hnot
      rw [← hr]
      change Additive.ofMul (Additive.toMul (realToDual r)
        (Multiplicative.ofAdd (t / r))) = Additive.ofMul (Real.fourierChar t)
      rw [realToDual_apply, div_eq_mul_inv, mul_left_comm r t r⁻¹,
        mul_inv_cancel₀ hr0, mul_one]
    simpa only [Real.dist_eq, sub_zero] using habs

/-- The forward continuous homomorphism of real self-duality is the Fourier family. -/
theorem realEquiv_toContinuousAddMonoidHom :
    (realEquiv : ℝ →ₜ+ Additive (PontryaginDual (Multiplicative ℝ))) = realToDual := rfl

/-- Real self-duality evaluates by the period-one Fourier kernel. -/
@[simp] theorem realEquiv_apply (r x : ℝ) :
    Additive.toMul (realEquiv r) (Multiplicative.ofAdd x) =
      Real.fourierChar (r * x) := rfl

private theorem realEquiv_apply_comm (a b : Multiplicative ℝ) :
    Additive.toMul (realEquiv a.toAdd) b = Additive.toMul (realEquiv b.toAdd) a := by
  change Additive.toMul (realEquiv a.toAdd) (Multiplicative.ofAdd b.toAdd) =
    Additive.toMul (realEquiv b.toAdd) (Multiplicative.ofAdd a.toAdd)
  rw [realEquiv_apply, realEquiv_apply, mul_comm]

/-- Canonical evaluation of the additive real line into its Pontryagin bidual is
bijective. See Neukirch–Schmidt–Wingberg, Chapter I, §1, (1.1.11). -/
theorem realEval_bijective : Function.Bijective (eval (Multiplicative ℝ)) := by
  let j : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ) :=
    { toMulEquiv := realEquiv.toAddEquiv.toMultiplicativeLeft
      continuous_toFun := continuous_toMul.comp (realEquiv.continuous.comp continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp
        (realEquiv.symm.continuous.comp continuous_ofMul) }
  have hj (a : Multiplicative ℝ) :
      map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
        (eval (Multiplicative ℝ) a) = j a := by
    apply PontryaginDual.ext
    intro x
    exact realEquiv_apply_comm x a
  have hmap : Function.Injective
      (map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))) := by
    intro χ ψ h
    apply PontryaginDual.ext
    intro η
    have hη := congrArg
      (fun ξ : PontryaginDual (Multiplicative ℝ) => ξ (j.symm η)) h
    change χ (j (j.symm η)) = ψ (j (j.symm η)) at hη
    simpa only [j.apply_symm_apply] using hη
  constructor
  · intro a b h
    apply j.injective
    rw [← hj a, ← hj b, h]
  · intro χ
    refine ⟨j.symm (map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ)) χ), ?_⟩
    apply hmap
    rw [hj, j.apply_symm_apply]

/-- Real biduality whose forward map is canonical evaluation, with the iterated
compact-open topology on the bidual. See Neukirch–Schmidt–Wingberg,
Chapter I, §1, (1.1.11). -/
noncomputable def realEvalEquiv :
    Multiplicative ℝ ≃ₜ* PontryaginDual (PontryaginDual (Multiplicative ℝ)) where
  toMulEquiv := MulEquiv.ofBijective (eval (Multiplicative ℝ)) realEval_bijective
  continuous_toFun := (eval (Multiplicative ℝ)).continuous
  continuous_invFun := by
    let j : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ) :=
      { toMulEquiv := realEquiv.toAddEquiv.toMultiplicativeLeft
        continuous_toFun := continuous_toMul.comp (realEquiv.continuous.comp continuous_toAdd)
        continuous_invFun := continuous_ofAdd.comp
          (realEquiv.symm.continuous.comp continuous_ofMul) }
    have hj (a : Multiplicative ℝ) :
        map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
          (eval (Multiplicative ℝ) a) = j a := by
      apply PontryaginDual.ext
      intro x
      exact realEquiv_apply_comm x a
    let e := MulEquiv.ofBijective (eval (Multiplicative ℝ)) realEval_bijective
    change Continuous e.symm
    have hinv : (e.symm : PontryaginDual (PontryaginDual (Multiplicative ℝ)) →
        Multiplicative ℝ) =
        fun χ => j.symm
          (map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ)) χ) := by
      funext χ
      apply j.injective
      rw [← hj (e.symm χ)]
      change map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))
          (e (e.symm χ)) = _
      rw [e.apply_symm_apply, j.apply_symm_apply]
    rw [hinv]
    exact j.symm.continuous.comp
      (map (j : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ))).continuous

/-- The forward continuous homomorphism of real biduality is canonical evaluation. -/
theorem realEvalEquiv_toContinuousMonoidHom :
    (realEvalEquiv : Multiplicative ℝ →ₜ*
      PontryaginDual (PontryaginDual (Multiplicative ℝ))) = eval (Multiplicative ℝ) := rfl

/-- Real biduality sends `a` to the character `χ ↦ χ a`. -/
@[simp] theorem realEvalEquiv_apply (a : Multiplicative ℝ)
    (χ : PontryaginDual (Multiplicative ℝ)) : realEvalEquiv a χ = χ a := rfl

/-- Canonical real bidual evaluation pairs a point with its Fourier character. -/
theorem realEvalEquiv_apply_realToDual (x r : ℝ) :
    realEvalEquiv (Multiplicative.ofAdd x) (Additive.toMul (realToDual r)) =
      Real.fourierChar (r * x) := rfl

end PontryaginDual
