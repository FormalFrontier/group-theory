/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.PontryaginDual.Discrete.Surjective
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Pontryagin biduality for discrete abelian groups

Canonical evaluation identifies a discrete abelian group with its compact-open
Pontryagin bidual. Characters separate points: first map a cyclic subgroup to the
circle, and then extend its character by divisibility of the circle and Baer's
criterion. Surjectivity is supplied by `PontryaginDual.eval_surjective_of_discrete`.

The equivalence uses the original group and compact-open topologies. Its inverse
is the inverse of the bijective evaluation homomorphism. Both directions and the
inverse commute with continuous homomorphisms between discrete abelian groups.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.11), for Pontryagin biduality.
* Mathlib's `GroupTheory.SpecificGroups.Cyclic`, for the homomorphism determined
  by a generator, and `RingTheory.RootsOfUnity.Complex`, for primitive roots.
* Mathlib's `GroupTheory.Divisible` and `Algebra.Category.Grp.Injective`, for
  transport of divisibility and Baer's criterion, and `Algebra.Group.TypeTags.Hom`,
  for the additive reinterpretation of group homomorphisms.
-/

@[expose] public section

universe u v

namespace PontryaginDual

/-- Circle-valued continuous characters separate points of a discrete abelian
group, so canonical evaluation in its Pontryagin bidual is injective. -/
theorem evalHom_injective_of_discrete (A : Type u) [CommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] : Function.Injective (evalHom A) := by
  classical
  intro x y hxy
  by_contra hne
  let a : A := x / y
  have ha : a ≠ 1 := fun h => hne (div_eq_one.mp h)
  let H : Subgroup A := Subgroup.zpowers a
  let aH : H := ⟨a, Subgroup.mem_zpowers a⟩
  have hgen : ∀ z : H, z ∈ Subgroup.zpowers aH := by
    intro z
    obtain ⟨k, hk⟩ := z.property
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  have horder : orderOf aH = orderOf a := Subgroup.orderOf_mk a _
  -- In infinite order, any nonidentity circle element can be the generator image.
  -- In finite order, choose a primitive root of exactly the required order.
  have hc : ∃ c : Circle, c ≠ 1 ∧ orderOf c ∣ orderOf aH := by
    by_cases h0 : orderOf a = 0
    · exact ⟨Circle.exp Real.pi, Circle.exp_pi_ne_one, by rw [horder, h0]; exact dvd_zero _⟩
    · let c : Circle := Circle.exp (2 * Real.pi / (orderOf a : ℝ))
      have h1 : orderOf a ≠ 1 := fun h => ha (orderOf_eq_one_iff.mp h)
      have hn : 1 < orderOf a := by omega
      have hcoe : Circle.coeHom c =
          Complex.exp (2 * Real.pi * Complex.I / (orderOf a : ℂ)) := by
        change Complex.exp (((2 * Real.pi / (orderOf a : ℝ) : ℝ) : ℂ) * Complex.I) = _
        congr 1
        push_cast
        ring
      have hp' : IsPrimitiveRoot (Circle.coeHom c) (orderOf a) := by
        rw [hcoe]
        exact Complex.isPrimitiveRoot_exp (orderOf a) h0
      have hp : IsPrimitiveRoot c (orderOf a) := hp'.of_map_of_injective Circle.coe_injective
      exact ⟨c, hp.ne_one hn, by rw [horder, ← hp.eq_orderOf]⟩
  obtain ⟨c, hc1, hcd⟩ := hc
  let χH : H →* Circle := monoidHomOfForallMemZpowers hgen hcd
  have hχH : χH aH = c := monoidHomOfForallMemZpowers_apply_gen hgen hcd
  -- Division data is transported locally from the reals to the original circle.
  have hexp : Function.Surjective Circle.expHom := by
    intro z
    obtain ⟨t, ht⟩ := Circle.exp_surjective z.toMul
    exact ⟨t, congrArg Additive.ofMul ht⟩
  let : DivisibleBy (Additive Circle) ℤ :=
    Function.Surjective.divisibleBy Circle.expHom hexp
      (fun t n => Circle.expHom.map_zsmul n t)
  have hi : Function.Injective (MonoidHom.toAdditive H.subtype) := by
    intro z w h
    exact congrArg Additive.ofMul (H.subtype_injective (congrArg Additive.toMul h))
  obtain ⟨L, hL⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) hi (MonoidHom.toAdditive χH)
  let ψ : A →* Circle := MonoidHom.toAdditive.symm L
  have hψ : ψ a = c := by
    have h := congrArg (fun f : Additive H →+ Additive Circle => f (Additive.ofMul aH)) hL
    have h' : ψ a = χH aH := congrArg Additive.toMul h
    exact h'.trans hχH
  let χ : PontryaginDual A :=
    { toMonoidHom := ψ
      continuous_toFun := continuous_of_discreteTopology }
  have heq : ψ x = ψ y := congrArg (fun Φ : PontryaginDual (PontryaginDual A) => Φ χ) hxy
  have hval : ψ a = 1 := by simp [a, _root_.map_div, heq]
  exact hc1 (hψ.symm.trans hval)

/-- Canonical evaluation is a continuous multiplicative equivalence from a
discrete abelian group to its compact-open Pontryagin bidual. -/
noncomputable def evalEquivOfDiscrete (A : Type u) [CommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] : A ≃ₜ* PontryaginDual (PontryaginDual A) where
  toMulEquiv := MulEquiv.ofBijective (evalHom A)
    ⟨evalHom_injective_of_discrete A, eval_surjective_of_discrete A⟩
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

variable {A : Type u} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- The function underlying the bidual equivalence is canonical evaluation. -/
theorem evalEquivOfDiscrete_coe : ⇑(evalEquivOfDiscrete A) = evalHom A := rfl

/-- Forgetting continuity and the inverse gives the evaluation homomorphism. -/
@[simp] theorem evalEquivOfDiscrete_toMonoidHom :
    (evalEquivOfDiscrete A : A →* PontryaginDual (PontryaginDual A)) = evalHom A := rfl

/-- The continuous homomorphism underlying the equivalence is evaluation. -/
@[simp] theorem evalEquivOfDiscrete_toContinuousMonoidHom :
    (evalEquivOfDiscrete A : A →ₜ* PontryaginDual (PontryaginDual A)) = eval A := rfl

/-- Evaluation pairs an element with a character. -/
@[simp] theorem evalEquivOfDiscrete_apply (a : A) (χ : PontryaginDual A) :
    evalEquivOfDiscrete A a χ = χ a := rfl

/-- Every character takes the inverse image of a bidual character to its value. -/
@[simp] theorem evalEquivOfDiscrete_symm_apply (Φ : PontryaginDual (PontryaginDual A))
    (χ : PontryaginDual A) : χ ((evalEquivOfDiscrete A).symm Φ) = Φ χ := by
  simpa only [evalEquivOfDiscrete_apply] using
    congrArg (fun Ψ : PontryaginDual (PontryaginDual A) => Ψ χ)
      ((evalEquivOfDiscrete A).apply_symm_apply Φ)

variable {B : Type v} [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]

/-- Bidual evaluation is natural for homomorphisms between discrete abelian groups. -/
theorem evalEquivOfDiscrete_naturality (f : A →ₜ* B) :
    (map (map f)).comp (evalEquivOfDiscrete A : A →ₜ* PontryaginDual (PontryaginDual A)) =
      (evalEquivOfDiscrete B : B →ₜ* PontryaginDual (PontryaginDual B)).comp f := by
  simpa only [evalEquivOfDiscrete_toContinuousMonoidHom] using eval_naturality f

/-- The naturality square evaluated at a group element. -/
theorem evalEquivOfDiscrete_naturality_apply (f : A →ₜ* B) (a : A) :
    map (map f) (evalEquivOfDiscrete A a) = evalEquivOfDiscrete B (f a) :=
  congrArg (fun g : A →ₜ* PontryaginDual (PontryaginDual B) => g a)
    (evalEquivOfDiscrete_naturality f)

/-- Inverse bidual evaluation also commutes with homomorphisms. -/
theorem evalEquivOfDiscrete_symm_naturality_apply (f : A →ₜ* B)
    (Φ : PontryaginDual (PontryaginDual A)) :
    (evalEquivOfDiscrete B).symm (map (map f) Φ) = f ((evalEquivOfDiscrete A).symm Φ) := by
  apply (evalEquivOfDiscrete B).injective
  rw [ContinuousMulEquiv.apply_symm_apply, ← evalEquivOfDiscrete_naturality_apply,
    ContinuousMulEquiv.apply_symm_apply]

/-- The naturality square for the inverse equivalences, as continuous homomorphisms. -/
theorem evalEquivOfDiscrete_symm_naturality (f : A →ₜ* B) :
    ((evalEquivOfDiscrete B).symm : PontryaginDual (PontryaginDual B) →ₜ* B).comp
        (map (map f)) =
      f.comp ((evalEquivOfDiscrete A).symm : PontryaginDual (PontryaginDual A) →ₜ* A) := by
  ext Φ
  exact evalEquivOfDiscrete_symm_naturality_apply f Φ

end PontryaginDual
