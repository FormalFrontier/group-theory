/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Formal Frontier Agents
-/
/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Tactic

public import GroupTheory.RepresentationInvariants
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Inhomogeneous cochains over a ring

For a linear representation of a monoid, the inhomogeneous cochains are functions
from finite tuples of monoid elements to the coefficient module. Their differential
uses the given action and alternating integer signs. Cohomology is the homology of
this complex in the category of modules.

Degree zero identifies with the submodule of the original coefficient module fixed
by every monoid element. For groups over a commutative ring, the complex and its
cohomology agree with Mathlib's group cohomology.

## References

The coordinate differential and the commutative-ring comparison follow Mathlib's
`RepresentationTheory/Homological/GroupCohomology/Basic` and `LowDegree`; the
square-zero proof uses coface identities and adapts the triangular finite-sum
cancellation in Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`,
by Joël Riou, Adam Topaz and Johan Commelin. The fixed-vector description reuses
`Representation.fixedSubmodule` from
`GroupTheory/RepresentationInvariants` and its comparison with Mathlib invariants.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace Rep

variable {R : Type u} {G : Type v} [Ring R] [Monoid G]

/-- The coordinate differential on inhomogeneous cochains. -/
def inhomogeneousCochains.d (A : Rep.{w} R G) (n : ℕ) :
    ModuleCat.of R ((Fin n → G) → A) ⟶ ModuleCat.of R ((Fin (n + 1) → G) → A) :=
  ModuleCat.ofHom
    { toFun f g :=
        A.ρ (g 0) (f fun i => g i.succ) +
          Finset.univ.sum fun j : Fin (n + 1) =>
            (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
      map_add' := by
        intro f h
        ext g
        simp [Finset.sum_add_distrib, add_add_add_comm]
      map_smul' := by
        intro r f
        ext g
        simp only [Pi.smul_apply, map_smul, smul_add, Finset.smul_sum, RingHom.id_apply]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact (smul_comm r ((-1 : ℤ) ^ ((j : ℕ) + 1))
          (f (Fin.contractNth j (· * ·) g))).symm }

private def inhomogeneousCochains.coface (A : Rep.{w} R G) (n : ℕ)
    (i : Fin (n + 2)) :
    ((Fin n → G) → A) →ₗ[R] ((Fin (n + 1) → G) → A) :=
  Fin.cases
    { toFun := fun f g => A.ρ (g 0) (f fun k => g k.succ)
      map_add' := by
        intro f f'
        funext g
        exact (A.ρ (g 0)).map_add _ _
      map_smul' := by
        intro r f
        funext g
        exact (A.ρ (g 0)).map_smul r _ }
    (fun j =>
      { toFun := fun f g => f (Fin.contractNth j (· * ·) g)
        map_add' := by intro f f'; rfl
        map_smul' := by intro r f; rfl }) i

private theorem inhomogeneousCochains.contractNth_tail (n : ℕ)
    (j : Fin (n + 1)) (g : Fin (n + 2) → G) :
    Fin.contractNth j (· * ·) (fun k => g k.succ) =
      fun k => Fin.contractNth j.succ (· * ·) g k.succ := by
  funext k
  simp only [Fin.contractNth, Fin.val_succ]
  split_ifs <;> first
  | omega
  | simp only [Fin.castSucc_succ]

private theorem inhomogeneousCochains.contractNth_contractNth (n : ℕ)
    (i j : Fin (n + 1)) (g : Fin (n + 2) → G) (h : (i : ℕ) ≤ j) :
    Fin.contractNth j (· * ·) (Fin.contractNth i.castSucc (· * ·) g) =
      Fin.contractNth i (· * ·) (Fin.contractNth j.succ (· * ·) g) := by
  funext k
  simp only [Fin.contractNth, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first
  | omega
  | simp only [Fin.castSucc_succ, mul_assoc]

private theorem inhomogeneousCochains.coface_comp (A : Rep.{w} R G) (n : ℕ)
    (i j : Fin (n + 2)) (h : (j : ℕ) ≤ i) (f : (Fin n → G) → A) :
    inhomogeneousCochains.coface A (n + 1) j.castSucc
        (inhomogeneousCochains.coface A n i f) =
      inhomogeneousCochains.coface A (n + 1) i.succ
        (inhomogeneousCochains.coface A n j f) := by
  revert i
  refine Fin.cases ?_ (fun j => ?_) j
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      ext g
      change
        A.ρ (g 0) (A.ρ (g (0 : Fin (n + 1)).succ)
          (f fun k => g k.succ.succ)) =
          A.ρ ((Fin.contractNth (0 : Fin (n + 2)) (· * ·) g) 0)
            (f fun k => Fin.contractNth (0 : Fin (n + 2)) (· * ·) g k.succ)
      have htail : (fun k : Fin n =>
          Fin.contractNth (0 : Fin (n + 2)) (· * ·) g k.succ) =
          fun k => g k.succ.succ := by
        funext k
        exact Fin.contractNth_apply_of_gt _ _ _ _ (by simp)
      rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, htail]
      change
        A.ρ (g 0) (A.ρ (g (0 : Fin (n + 1)).succ) (f fun k => g k.succ.succ)) =
          A.ρ (g 0 * g (0 : Fin (n + 1)).succ) (f fun k => g k.succ.succ)
      rw [map_mul, Module.End.mul_apply]
    · intro h
      ext g
      change
        A.ρ (g 0) (f (Fin.contractNth i (· * ·) (fun k => g k.succ))) =
          A.ρ ((Fin.contractNth i.succ (· * ·) g) 0)
            (f (fun k => Fin.contractNth i.succ (· * ·) g k.succ))
      rw [Fin.contractNth_apply_of_lt i.succ (· * ·) g 0 (by simp)]
      rw [inhomogeneousCochains.contractNth_tail]
      simp only [Fin.castSucc_zero]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      simp only [Fin.val_zero, Fin.val_succ] at h
      omega
    · intro h
      ext g
      change
        f (Fin.contractNth i (· * ·) (Fin.contractNth j.castSucc (· * ·) g)) =
          f (Fin.contractNth j (· * ·) (Fin.contractNth i.succ (· * ·) g))
      exact congrArg f
        (inhomogeneousCochains.contractNth_contractNth n j i g (by simpa using h))

private theorem inhomogeneousCochains.d_apply_eq_sum_coface
    (A : Rep.{w} R G) (n : ℕ) (f : (Fin n → G) → A)
    (g : Fin (n + 1) → G) :
    inhomogeneousCochains.d A n f g =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        inhomogeneousCochains.coface A n i f g := by
  change
    A.ρ (g 0) (f fun k => g k.succ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) •
          f (Fin.contractNth j (· * ·) g) = _
  conv_rhs => rw [Fin.sum_univ_succ]
  simp [inhomogeneousCochains.coface]

private theorem inhomogeneousCochains.d_comp_d (A : Rep.{w} R G) (n : ℕ) :
    inhomogeneousCochains.d A n ≫ inhomogeneousCochains.d A (n + 1) = 0 := by
  classical
  ext f g
  change inhomogeneousCochains.d A (n + 1) (inhomogeneousCochains.d A n f) g = 0
  have hd : inhomogeneousCochains.d A n f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        inhomogeneousCochains.coface A n i f := by
    funext g'
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      inhomogeneousCochains.d_apply_eq_sum_coface A n f g'
  rw [inhomogeneousCochains.d_apply_eq_sum_coface A (n + 1), hd]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  let P := Fin (n + 2) × Fin (n + 3)
  let t : P → A := fun ij =>
    ((-1 : ℤ) ^ (ij.2 : ℕ) * (-1 : ℤ) ^ (ij.1 : ℕ)) •
      inhomogeneousCochains.coface A (n + 1) ij.2
        (inhomogeneousCochains.coface A n ij.1 f) g
  change (∑ ij : P, t ij) = 0
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp [t]
    simp only [← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_mul,
        neg_neg, mul_one]
      apply mul_comm
    · have hji : (j : ℕ) ≤ i := (Finset.mem_filter.mp hij).right
      have hc := inhomogeneousCochains.coface_comp A n i
        (Fin.castLT j (lt_of_le_of_lt hji i.isLt)) hji f
      simpa only [φ, Fin.castSucc_castLT] using congrArg (fun q => q g) hc

/-- The complex of inhomogeneous cochains of a linear monoid representation. -/
def inhomogeneousCochains (A : Rep.{w} R G) :
    CochainComplex (ModuleCat.{max v w} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d A n)
    (fun n => by exact inhomogeneousCochains.d_comp_d A n)

/-- The degree `n` cochains are functions on `n`-tuples, with the pointwise module. -/
@[simp] theorem inhomogeneousCochains_X (A : Rep.{w} R G) (n : ℕ) :
    (inhomogeneousCochains A).X n = ModuleCat.of R ((Fin n → G) → A) := by
  rfl

/-- The differential evaluated on a tuple is the alternating face formula. -/
theorem inhomogeneousCochains_d_apply (A : Rep.{w} R G) (n : ℕ)
    (f : (Fin n → G) → A) (g : Fin (n + 1) → G) :
    (inhomogeneousCochains A).d n (n + 1) f g =
      A.ρ (g 0) (f fun i => g i.succ) +
        Finset.univ.sum fun j : Fin (n + 1) =>
          (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
  simp only [inhomogeneousCochains, CochainComplex.of_d]
  rfl

/-- Cohomology of a linear monoid representation, computed by its cochain complex. -/
def cohomology (A : Rep.{w} R G) (n : ℕ) : ModuleCat.{max v w} R :=
  (inhomogeneousCochains A).homology n

/-- Cohomology is the canonical homology of the inhomogeneous cochain complex. -/
theorem cohomology_eq_homology (A : Rep.{w} R G) (n : ℕ) :
    cohomology A n = (inhomogeneousCochains A).homology n := by
  rfl

private theorem inhomogeneousCochains_d_zero_apply (A : Rep.{w} R G)
    (f : (Fin 0 → G) → A) (g : G) :
    (inhomogeneousCochains A).d 0 1 f (fun _ : Fin 1 => g) =
      A.ρ g (f Fin.elim0) - f Fin.elim0 := by
  have hf : ∀ t : Fin 0 → G, f t = f Fin.elim0 :=
    fun t => congrArg f (Subsingleton.elim _ _)
  simp [inhomogeneousCochains_d_apply, hf, sub_eq_add_neg]

private theorem inhomogeneousCochains_constant_cocycle (A : Rep.{w} R G)
    (x : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
    ((inhomogeneousCochains A).d 0 1).hom
      (fun _ : Fin 0 → G => (x : A)) = 0 := by
  change (fun t : Fin 1 → G =>
    (inhomogeneousCochains A).d 0 1
      (fun _ : Fin 0 → G => (x : A)) t) = fun _ => (0 : A)
  funext t
  rw [inhomogeneousCochains_d_apply]
  simp [Representation.apply_coe_fixedSubmodule]

private theorem inhomogeneousCochains_iCycles_constant (A : Rep.{w} R G)
    (x : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
    ((inhomogeneousCochains A).iCycles 0).hom
      ((inhomogeneousCochains A).cyclesMk
        (fun _ : Fin 0 → G => (x : A)) 1 (by simp)
        (by exact inhomogeneousCochains_constant_cocycle A x)) =
      (fun _ : Fin 0 → G => (x : A)) := by
  exact HomologicalComplex.i_cyclesMk (inhomogeneousCochains A)
    (fun _ : Fin 0 → G => (x : A)) 1 (by simp)
    (by exact inhomogeneousCochains_constant_cocycle A x)

/-- The degree-zero cohomology class of a constant cochain with fixed value. -/
def cohomologyZeroClass (A : Rep.{w} R G) :
    ↥(A.ρ.fixedSubmodule : Submodule R A) →ₗ[R] cohomology A 0 where
  toFun x :=
    (inhomogeneousCochains A).homologyπ 0
      ((inhomogeneousCochains A).cyclesMk
        (fun _ : Fin 0 → G => (x : A)) 1 (by simp) (by
          exact inhomogeneousCochains_constant_cocycle A x))
  map_add' x y := by
    let c (z : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
        (inhomogeneousCochains A).cycles 0 :=
      (inhomogeneousCochains A).cyclesMk
        (fun _ : Fin 0 → G => (z : A)) 1 (by simp)
        (by exact inhomogeneousCochains_constant_cocycle A z)
    have hc (z : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
        ((inhomogeneousCochains A).iCycles 0).hom (c z) =
          (fun _ : Fin 0 → G => (z : A)) := by
      exact HomologicalComplex.i_cyclesMk (inhomogeneousCochains A)
        (fun _ : Fin 0 → G => (z : A)) 1 (by simp)
        (by exact inhomogeneousCochains_constant_cocycle A z)
    have hadd : c (x + y) = c x + c y := by
      apply (ModuleCat.mono_iff_injective
        ((inhomogeneousCochains A).iCycles 0)).1 inferInstance
      have hsum :
          (fun _ : Fin 0 → G => ((x + y : ↥(A.ρ.fixedSubmodule : Submodule R A)) : A)) =
            ((inhomogeneousCochains A).iCycles 0).hom (c x) +
              ((inhomogeneousCochains A).iCycles 0).hom (c y) :=
        congrArg₂ (fun f g : (Fin 0 → G) → A => f + g) (hc x).symm (hc y).symm
      exact Eq.trans (hc (x + y))
        (Eq.trans hsum
          (((inhomogeneousCochains A).iCycles 0).hom.map_add (c x) (c y)).symm)
    exact (congrArg ((inhomogeneousCochains A).homologyπ 0).hom hadd).trans
      (((inhomogeneousCochains A).homologyπ 0).hom.map_add (c x) (c y))
  map_smul' r x := by
    let c (z : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
        (inhomogeneousCochains A).cycles 0 :=
      (inhomogeneousCochains A).cyclesMk
        (fun _ : Fin 0 → G => (z : A)) 1 (by simp)
        (by exact inhomogeneousCochains_constant_cocycle A z)
    have hc (z : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
        ((inhomogeneousCochains A).iCycles 0).hom (c z) =
          (fun _ : Fin 0 → G => (z : A)) := by
      exact HomologicalComplex.i_cyclesMk (inhomogeneousCochains A)
        (fun _ : Fin 0 → G => (z : A)) 1 (by simp)
        (by exact inhomogeneousCochains_constant_cocycle A z)
    have hsmul : c (r • x) = r • c x := by
      apply (ModuleCat.mono_iff_injective
        ((inhomogeneousCochains A).iCycles 0)).1 inferInstance
      have hscale :
          (fun _ : Fin 0 → G => ((r • x : ↥(A.ρ.fixedSubmodule : Submodule R A)) : A)) =
            r • ((inhomogeneousCochains A).iCycles 0).hom (c x) :=
        congrArg (fun f : (Fin 0 → G) → A => r • f) (hc x).symm
      exact Eq.trans (hc (r • x))
        (Eq.trans hscale
          (((inhomogeneousCochains A).iCycles 0).hom.map_smul r (c x)).symm)
    exact (congrArg ((inhomogeneousCochains A).homologyπ 0).hom hsmul).trans
      (((inhomogeneousCochains A).homologyπ 0).hom.map_smul r (c x))

private theorem cohomologyZeroClass_bijective (A : Rep.{w} R G) :
    Function.Bijective (cohomologyZeroClass A) := by
  constructor
  · intro x y h
    apply Subtype.ext
    dsimp only [cohomologyZeroClass] at h
    have hc := (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).homologyπ 0)).1 inferInstance h
    have hi := congrArg ((inhomogeneousCochains A).iCycles 0).hom hc
    have hxy : (fun _ : Fin 0 → G => (x : A)) =
        (fun _ : Fin 0 → G => (y : A)) :=
      Eq.trans (inhomogeneousCochains_iCycles_constant A x).symm
        (Eq.trans hi (inhomogeneousCochains_iCycles_constant A y))
    exact congrFun hxy Fin.elim0
  · intro z
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((inhomogeneousCochains A).homologyπ 0)).1 inferInstance z
    let f : (Fin 0 → G) → A := (inhomogeneousCochains A).iCycles 0 c
    have hdf : (inhomogeneousCochains A).d 0 1 f = 0 := by
      have h := congrArg
        (fun φ : (inhomogeneousCochains A).cycles 0 ⟶
          (inhomogeneousCochains A).X 1 => φ c)
        ((inhomogeneousCochains A).iCycles_d 0 1)
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h
    have ha : f Fin.elim0 ∈ A.ρ.fixedSubmodule := by
      rw [Representation.mem_fixedSubmodule]
      intro g
      have h := congrFun hdf (fun _ : Fin 1 => g)
      rw [inhomogeneousCochains_d_zero_apply] at h
      exact sub_eq_zero.mp h
    refine ⟨⟨f Fin.elim0, ha⟩, ?_⟩
    dsimp only [cohomologyZeroClass]
    change (inhomogeneousCochains A).homologyπ 0 _ =
      (inhomogeneousCochains A).homologyπ 0 c
    apply congrArg ((inhomogeneousCochains A).homologyπ 0)
    apply (ModuleCat.mono_iff_injective
      ((inhomogeneousCochains A).iCycles 0)).1 inferInstance
    exact Eq.trans
      (inhomogeneousCochains_iCycles_constant A ⟨f Fin.elim0, ha⟩)
      (show (fun _ : Fin 0 → G => f Fin.elim0) = f from
        funext fun t => congrArg f (Subsingleton.elim _ _))

/-- Degree-zero cohomology is the fixed-vector submodule of the coefficient module. -/
def cohomologyZeroEquiv (A : Rep.{w} R G) :
    cohomology A 0 ≃ₗ[R] ↥(A.ρ.fixedSubmodule : Submodule R A) :=
  (LinearEquiv.ofBijective (cohomologyZeroClass A)
    (by exact cohomologyZeroClass_bijective A)).symm

/-- The inverse of the degree-zero identification takes a fixed vector to its constant class. -/
@[simp] theorem cohomologyZeroEquiv_symm_apply (A : Rep.{w} R G)
    (x : ↥(A.ρ.fixedSubmodule : Submodule R A)) :
    (cohomologyZeroEquiv A).symm x = cohomologyZeroClass A x := by
  rfl

section Invariants

variable {R : Type u} {G : Type v} [CommRing R] [Group G]

/-- Degree-zero cohomology identifies with the invariant submodule of the given action. -/
def cohomologyZeroEquivInvariants (A : Rep.{w} R G) :
    cohomology A 0 ≃ₗ[R] A.ρ.invariants where
  toFun x := ⟨(cohomologyZeroEquiv A x : A), by
    rw [← Representation.fixedSubmodule_eq_invariants]
    exact (cohomologyZeroEquiv A x).property⟩
  invFun x := (cohomologyZeroEquiv A).symm ⟨(x : A), by
    rw [Representation.fixedSubmodule_eq_invariants]
    exact x.property⟩
  left_inv x := by
    exact (cohomologyZeroEquiv A).symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    simp only [LinearEquiv.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext
    exact congrArg (fun z : ↥(A.ρ.fixedSubmodule : Submodule R A) => (z : A))
      ((cohomologyZeroEquiv A).map_add x y)
  map_smul' r x := by
    apply Subtype.ext
    exact congrArg (fun z : ↥(A.ρ.fixedSubmodule : Submodule R A) => (z : A))
      ((cohomologyZeroEquiv A).map_smul r x)

/-- Both degree-zero identifications have the same value in the original coefficient module. -/
@[simp] theorem cohomologyZeroEquivInvariants_apply (A : Rep.{w} R G)
    (x : cohomology A 0) :
    (cohomologyZeroEquivInvariants A x : A) = (cohomologyZeroEquiv A x : A) := by
  rfl

end Invariants

section GroupCohomology

variable {R G : Type u} [CommRing R] [Group G] (A : Rep.{u} R G)

private theorem inhomogeneousCochains_d_eq (n : ℕ) :
    inhomogeneousCochains.d A n = _root_.inhomogeneousCochains.d A n := by
  ext f g
  change
    A.ρ (g 0) (f fun i => g i.succ) +
        (Finset.univ.sum fun j : Fin (n + 1) =>
          (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      A.ρ (g 0) (f fun i => g i.succ) +
        (Finset.univ.sum fun j : Fin (n + 1) =>
          (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g))
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Under the commutative-ring hypotheses, the coordinate complex is Mathlib's complex. -/
theorem inhomogeneousCochains_eq :
    inhomogeneousCochains A = groupCohomology.inhomogeneousCochains A := by
  refine HomologicalComplex.ext
    (C₁ := inhomogeneousCochains A)
    (C₂ := groupCohomology.inhomogeneousCochains A) rfl ?_
  intro i j hij
  have hj : i + 1 = j := hij
  subst j
  simp only [inhomogeneousCochains, CochainComplex.of_d]
  change inhomogeneousCochains.d A i ≫
      (𝟙 (ModuleCat.of R ((Fin (i + 1) → G) → A))) =
    (𝟙 (ModuleCat.of R ((Fin i → G) → A))) ≫
      _root_.inhomogeneousCochains.d A i
  simpa only [Category.comp_id, Category.id_comp] using
    inhomogeneousCochains_d_eq A i

/-- Under the commutative-ring hypotheses, cohomology agrees with Mathlib's group cohomology. -/
theorem cohomology_eq (n : ℕ) : cohomology A n = groupCohomology A n := by
  exact congrArg
    (fun C : CochainComplex (ModuleCat R) ℕ => C.homology n)
    (inhomogeneousCochains_eq A)

/-- The degree-zero equivalence agrees with Mathlib's identification in the coefficient module. -/
theorem cohomologyZeroEquivInvariants_eq_H0Iso (x : cohomology A 0) :
    (cohomologyZeroEquivInvariants A x : A) =
      ((groupCohomology.H0Iso A).hom (eqToHom (cohomology_eq A 0) x) : A) := by
  let e : inhomogeneousCochains A ⟶ groupCohomology.inhomogeneousCochains A :=
    eqToHom (inhomogeneousCochains_eq A)
  have heH : HomologicalComplex.homologyMap e 0 = eqToHom (cohomology_eq A 0) := by
    exact eqToHom_map
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) 0)
      (inhomogeneousCochains_eq A)
  -- Work with the homology functor's map, and convert back to the public transport once.
  suffices h : (cohomologyZeroEquivInvariants A x : A) =
      ((groupCohomology.H0Iso A).hom (HomologicalComplex.homologyMap e 0 x) : A) by
    exact h.trans (congrArg
      (fun f : cohomology A 0 ⟶ groupCohomology A 0 =>
        ((groupCohomology.H0Iso A).hom (f x) : A)) heH)
  have he0 : e.f 0 = 𝟙 ((inhomogeneousCochains A).X 0) := by
    dsimp only [e]
    rw [HomologicalComplex.eqToHom_f]
    change (eqToHom _ : ModuleCat.of R ((Fin 0 → G) → A) ⟶
      ModuleCat.of R ((Fin 0 → G) → A)) = 𝟙 _
    rfl
  have hnat :
      (inhomogeneousCochains A).homologyπ 0 ≫ HomologicalComplex.homologyMap e 0 =
        HomologicalComplex.cyclesMap e 0 ≫ groupCohomology.π A 0 :=
    HomologicalComplex.homologyπ_naturality e 0
  have hπ :
      groupCohomology.π A 0 ≫ (groupCohomology.H0Iso A).hom ≫
          (groupCohomology.shortComplexH0 A).f =
        groupCohomology.iCocycles A 0 ≫ (groupCohomology.cochainsIso₀ A).hom := by
    have h₁ :
        groupCohomology.π A 0 ≫ (groupCohomology.H0Iso A).hom ≫
            (groupCohomology.shortComplexH0 A).f =
          (groupCohomology.cocyclesIso₀ A).hom ≫
            (groupCohomology.shortComplexH0 A).f := by
      exact Eq.trans (Category.assoc _ _ _).symm (congrArg
        (fun f : groupCohomology.cocycles A 0 ⟶ ModuleCat.of R A.ρ.invariants =>
          f ≫ (groupCohomology.shortComplexH0 A).f)
        (groupCohomology.π_comp_H0Iso_hom A))
    exact Eq.trans h₁ (groupCohomology.cocyclesIso₀_hom_comp_f A)
  have hcomp :
      (inhomogeneousCochains A).homologyπ 0 ≫ HomologicalComplex.homologyMap e 0 ≫
          (groupCohomology.H0Iso A).hom ≫ (groupCohomology.shortComplexH0 A).f =
        (inhomogeneousCochains A).iCycles 0 ≫ (groupCohomology.cochainsIso₀ A).hom := by
    have h₁ :
        (inhomogeneousCochains A).homologyπ 0 ≫ HomologicalComplex.homologyMap e 0 ≫
            (groupCohomology.H0Iso A).hom ≫ (groupCohomology.shortComplexH0 A).f =
          HomologicalComplex.cyclesMap e 0 ≫
            (groupCohomology.π A 0 ≫ (groupCohomology.H0Iso A).hom ≫
              (groupCohomology.shortComplexH0 A).f) := by
      exact Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg
            (fun f : (inhomogeneousCochains A).cycles 0 ⟶ groupCohomology A 0 =>
              f ≫ (groupCohomology.H0Iso A).hom ≫
                (groupCohomology.shortComplexH0 A).f) hnat)
          (Category.assoc _ _ _))
    have h₂ :
        HomologicalComplex.cyclesMap e 0 ≫
            (groupCohomology.π A 0 ≫ (groupCohomology.H0Iso A).hom ≫
              (groupCohomology.shortComplexH0 A).f) =
          HomologicalComplex.cyclesMap e 0 ≫
            (groupCohomology.iCocycles A 0 ≫ (groupCohomology.cochainsIso₀ A).hom) :=
      congrArg
        (fun f : groupCohomology.cocycles A 0 ⟶ ModuleCat.of R A =>
          HomologicalComplex.cyclesMap e 0 ≫ f) hπ
    have hi : (inhomogeneousCochains A).iCycles 0 ≫ e.f 0 =
        (inhomogeneousCochains A).iCycles 0 :=
      Eq.trans
        (congrArg
          (fun f : ModuleCat.of R ((Fin 0 → G) → A) ⟶
              ModuleCat.of R ((Fin 0 → G) → A) =>
            (inhomogeneousCochains A).iCycles 0 ≫ f) he0)
        (Category.comp_id _)
    have h₃ :
        HomologicalComplex.cyclesMap e 0 ≫
            (groupCohomology.iCocycles A 0 ≫ (groupCohomology.cochainsIso₀ A).hom) =
          (inhomogeneousCochains A).iCycles 0 ≫ (groupCohomology.cochainsIso₀ A).hom := by
      exact Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg
            (fun f : (inhomogeneousCochains A).cycles 0 ⟶
                ModuleCat.of R ((Fin 0 → G) → A) =>
              f ≫ (groupCohomology.cochainsIso₀ A).hom)
            (HomologicalComplex.cyclesMap_i e 0))
          (congrArg
            (fun f : (inhomogeneousCochains A).cycles 0 ⟶
                ModuleCat.of R ((Fin 0 → G) → A) =>
              f ≫ (groupCohomology.cochainsIso₀ A).hom) hi))
    exact Eq.trans h₁ (Eq.trans h₂ h₃)
  have hvalue (z : (inhomogeneousCochains A).cycles 0) :
      ((groupCohomology.H0Iso A).hom
          (HomologicalComplex.homologyMap e 0
            ((inhomogeneousCochains A).homologyπ 0 z)) : A) =
        (inhomogeneousCochains A).iCycles 0 z default := by
    have hz := congrArg
      (fun f : (inhomogeneousCochains A).cycles 0 ⟶ ModuleCat.of R A => f z) hcomp
    change
      ((groupCohomology.H0Iso A).hom
          (HomologicalComplex.homologyMap e 0
            ((inhomogeneousCochains A).homologyπ 0 z)) : A) =
        (inhomogeneousCochains A).iCycles 0 z default at hz
    exact hz
  obtain ⟨y, rfl⟩ := (cohomologyZeroEquiv A).symm.surjective x
  rw [cohomologyZeroEquivInvariants_apply, LinearEquiv.apply_symm_apply,
    cohomologyZeroEquiv_symm_apply]
  dsimp only [cohomologyZeroClass]
  refine Eq.trans ?_ (hvalue _).symm
  have hc :
      ((inhomogeneousCochains A).iCycles 0).hom
        ((inhomogeneousCochains A).cyclesMk
          (fun _ : Fin 0 → G => (y : A)) 1 (by simp)
          (by exact inhomogeneousCochains_constant_cocycle A y)) =
        (fun _ : Fin 0 → G => (y : A)) := by
    exact HomologicalComplex.i_cyclesMk (inhomogeneousCochains A)
      (fun _ : Fin 0 → G => (y : A)) 1 (by simp)
      (by exact inhomogeneousCochains_constant_cocycle A y)
  exact (congrFun hc default).symm

end GroupCohomology

end Rep
