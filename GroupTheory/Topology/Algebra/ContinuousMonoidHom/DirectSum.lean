/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Continuous homomorphisms on discrete direct sums

Restriction to the summands identifies the compact-open space of continuous
homomorphisms on a discrete direct sum with the product of the factor hom spaces.

The inverse uses Mathlib's `DirectSum.toAddMonoid`. The topological comparison
uses `ContinuousMap.homeoFnOfDiscrete`; continuity of evaluations follows by
finite-support induction.
-/

@[expose] public section

open scoped BigOperators DirectSum

universe u v w

namespace ContinuousMonoidHom

/-- Restriction to the summands of a discrete direct sum, with inverse given by
extension of the factor homomorphisms. All hom spaces carry compact-open topology. -/
noncomputable def directSumEquivPi
    {ι : Type u} (A : ι → Type v) (D : Type w)
    [∀ i, AddCommMonoid (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
    [TopologicalSpace (⨁ i, A i)] [DiscreteTopology (⨁ i, A i)]
    [CommMonoid D] [TopologicalSpace D] [ContinuousMul D] :
    (Multiplicative (⨁ i, A i) →ₜ* D) ≃ₜ*
      (∀ i, Multiplicative (A i) →ₜ* D) := by
  classical
  let inclusion (i : ι) : Multiplicative (A i) →ₜ* Multiplicative (⨁ i, A i) :=
    { toMonoidHom := (DirectSum.of A i).toMultiplicative
      continuous_toFun := continuous_of_discreteTopology }
  let lift (f : ∀ i, Multiplicative (A i) →ₜ* D) :
      Multiplicative (⨁ i, A i) →ₜ* D :=
    { toMonoidHom :=
        (DirectSum.toAddMonoid fun i => (f i).toMonoidHom.toAdditive).toMultiplicative
      continuous_toFun := continuous_of_discreteTopology }
  have hlift_of (f : ∀ i, Multiplicative (A i) →ₜ* D) (i : ι) (a : A i) :
      lift f (Multiplicative.ofAdd (DirectSum.of A i a)) =
        f i (Multiplicative.ofAdd a) := by
    change Additive.toMul
      ((DirectSum.toAddMonoid (fun j => (f j).toMonoidHom.toAdditive))
        (DirectSum.of A i a)) = _
    exact congrArg Additive.toMul
      (DirectSum.toAddMonoid_of (φ := fun j => (f j).toMonoidHom.toAdditive) i a)
  have hforgetSum : Topology.IsInducing
      (fun f : Multiplicative (⨁ i, A i) →ₜ* D => f.toContinuousMap) := ⟨rfl⟩
  have hforgetFactor (i : ι) : Topology.IsInducing
      (fun f : Multiplicative (A i) →ₜ* D => f.toContinuousMap) := ⟨rfl⟩
  have continuous_lift : Continuous lift := by
    have heval (i : ι) (a : Multiplicative (A i)) :
        Continuous (fun f : ∀ i, Multiplicative (A i) →ₜ* D => f i a) := by
      have h : Continuous
          (fun f : ∀ i, Multiplicative (A i) →ₜ* D => (f i).toContinuousMap a) := by
        simpa only [Function.comp_def, ContinuousMap.coe_homeoFnOfDiscrete] using
          (continuous_apply a).comp
            ((ContinuousMap.homeoFnOfDiscrete).continuous.comp
              ((hforgetFactor i).continuous.comp (continuous_apply i)))
      convert h using 1
    have hpoint (x : ⨁ i, A i) :
        Continuous (fun f : ∀ i, Multiplicative (A i) →ₜ* D =>
          lift f (Multiplicative.ofAdd x)) := by
      refine DirectSum.induction_on x ?_ ?_ ?_
      · change Continuous (fun f : ∀ i, Multiplicative (A i) →ₜ* D =>
          lift f 1)
        simpa only [map_one] using
          (continuous_const : Continuous
            (fun _ : ∀ i, Multiplicative (A i) →ₜ* D => (1 : D)))
      · intro i a
        have hgen :
            (fun f : ∀ i, Multiplicative (A i) →ₜ* D =>
              lift f (Multiplicative.ofAdd (DirectSum.of A i a))) =
            (fun f => f i (Multiplicative.ofAdd a)) :=
          funext (fun f => hlift_of f i a)
        rw [hgen]
        exact heval i (Multiplicative.ofAdd a)
      · intro x y hx hy
        change Continuous (fun f : ∀ i, Multiplicative (A i) →ₜ* D =>
          lift f (Multiplicative.ofAdd x * Multiplicative.ofAdd y))
        simpa only [map_mul, Pi.mul_def] using hx.mul hy
    apply hforgetSum.continuous_iff.mpr
    apply (ContinuousMap.homeoFnOfDiscrete).isInducing.continuous_iff.mpr
    have h : Continuous
        (fun f : ∀ i, Multiplicative (A i) →ₜ* D =>
          fun x : Multiplicative (⨁ i, A i) =>
            lift f (Multiplicative.ofAdd (Multiplicative.toAdd x))) :=
      continuous_pi fun x => hpoint (Multiplicative.toAdd x)
    convert h using 1
    funext f x
    simp only [Function.comp_def, ContinuousMap.coe_homeoFnOfDiscrete]
    rfl
  exact
    { toMulEquiv :=
        { toFun := fun f i => f.comp (inclusion i)
          invFun := lift
          left_inv := by
            intro f
            ext x
            change Additive.toMul
                (DirectSum.toAddMonoid (fun i =>
                  f.toMonoidHom.toAdditive.comp (DirectSum.of A i))
                  (Multiplicative.toAdd x)) =
              Additive.toMul (f.toMonoidHom.toAdditive (Multiplicative.toAdd x))
            exact congrArg Additive.toMul
              (DirectSum.toAddMonoid.unique (ψ := f.toMonoidHom.toAdditive)
                (Multiplicative.toAdd x)).symm
          right_inv := by
            intro f
            funext i
            ext a
            change lift f (Multiplicative.ofAdd
                (DirectSum.of A i (Multiplicative.toAdd a))) = f i a
            convert hlift_of f i (Multiplicative.toAdd a) using 1
            rfl
          map_mul' := by
            intro f g
            funext i
            ext a
            rfl }
      continuous_toFun :=
        continuous_pi fun i => continuous_comp_left (inclusion i)
      continuous_invFun := continuous_lift }

variable {ι : Type u} {A : ι → Type v} {D : Type w}
variable [∀ i, AddCommMonoid (A i)]
variable [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
variable [TopologicalSpace (⨁ i, A i)] [DiscreteTopology (⨁ i, A i)]
variable [CommMonoid D] [TopologicalSpace D] [ContinuousMul D]

open scoped Classical in
@[simp] theorem directSumEquivPi_apply
    (f : Multiplicative (⨁ i, A i) →ₜ* D) (i : ι) (a : A i) :
    directSumEquivPi A D f i (Multiplicative.ofAdd a) =
      f (Multiplicative.ofAdd (DirectSum.of A i a)) := by
  rfl

open scoped Classical in
@[simp] theorem directSumEquivPi_symm_apply_of
    (f : ∀ i, Multiplicative (A i) →ₜ* D) (i : ι) (a : A i) :
    (directSumEquivPi A D).symm f
        (Multiplicative.ofAdd (DirectSum.of A i a)) =
      f i (Multiplicative.ofAdd a) := by
  have h := congrArg (fun g => g i (Multiplicative.ofAdd a))
    ((directSumEquivPi A D).apply_symm_apply f)
  simpa only [directSumEquivPi_apply] using h

open scoped Classical in
/-- Evaluation of an extended family on a finite-support sum. -/
theorem directSumEquivPi_symm_apply
    (f : ∀ i, Multiplicative (A i) →ₜ* D) (x : ⨁ i, A i) :
    (directSumEquivPi A D).symm f (Multiplicative.ofAdd x) =
      ∏ i ∈ x.support, f i (Multiplicative.ofAdd (x i)) := by
  classical
  calc
    (directSumEquivPi A D).symm f (Multiplicative.ofAdd x) =
        (directSumEquivPi A D).symm f
          (∏ i ∈ x.support, Multiplicative.ofAdd (DirectSum.of A i (x i))) := by
      congr 1
      simpa using congrArg Multiplicative.ofAdd (DirectSum.sum_support_of x).symm
    _ = ∏ i ∈ x.support, f i (Multiplicative.ofAdd (x i)) := by
      simp only [map_prod, directSumEquivPi_symm_apply_of]

end ContinuousMonoidHom
