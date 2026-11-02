/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
import GroupTheory.Topology.Algebra.ContinuousAddMonoidHom.Extension
import GroupTheory.Topology.TypeTags
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.Monoid

/-!
# Restriction of Circle characters to open subgroups

Every continuous Circle character of an open subgroup of a commutative group extends to the
whole group. The ambient topology need only make left translations continuous: commutativity
then gives separate continuity of multiplication. The subgroup carries its induced topology.

The restriction map is the existing `PontryaginDual.map` applied to the subgroup inclusion.
Its surjectivity asserts existence of extensions, not uniqueness or a continuous, homomorphic,
or natural choice of extensions. No separation or local compactness assumption is needed,
and no biduality assertion is made here.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected second edition,
  Chapter I, §1D, for the surrounding Pontryagin-duality context.
* Divisible-abelian-group injectivity, as formalized in Mathlib by Jujian Zhang, supplies
  the algebraic step in `ContinuousAddMonoidHom.exists_extension_of_isOpen`.
* Mathlib's Circle and exponential formalizations by Heather Macbeth and Yury Kudryashov
  supply integer divisibility through the surjective exponential.
* Mathlib's canonical tags (Mario Carneiro), subgroup theory (Kexing Ying), topology
  constructions (Johannes Hölzl, Mario Carneiro and Patrick Massot), and continuous-hom and
  Pontryagin-dual formalizations (Thomas Browning and Nailin Guan) supply the underlying API.
  `GroupTheory.Topology.TypeTags` supplies the continuous one-sided tag conversion.
-/

@[expose] public section

universe u

/-- Restriction to an open subgroup is surjective on continuous Circle characters of a
commutative group whose left translations are continuous. The subgroup has its induced topology.

This is the open-subgroup character-extension step in Pontryagin duality; see Neukirch,
Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1D for context. The proof
uses divisible-abelian-group injectivity through the existing continuous additive extension
theorem, reusing Mathlib's division and Circle exponential formalizations. -/
theorem PontryaginDual.map_subtype_surjective_of_isOpen
    {A : Type u} [CommGroup A] [TopologicalSpace A] [ContinuousConstSMul A A]
    (H : Subgroup A) (hH : IsOpen (H : Set A)) :
    Function.Surjective
      (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* A)) := by
  have : SeparatelyContinuousMul A :=
    { continuous_const_mul := fun {a} ↦ continuous_const_smul a
      continuous_mul_const := fun {a} ↦ by
        simpa [smul_eq_mul, mul_comm] using
          (continuous_const_smul a : Continuous (fun x : A ↦ a • x)) }
  let _ : DivisibleBy (Additive Circle) ℤ := by
    first
    | infer_instance
    | have hExp : Function.Surjective Circle.expHom := by
        intro z
        obtain ⟨t, ht⟩ := Circle.exp_surjective z.toMul
        exact ⟨t, congrArg Additive.ofMul ht⟩
      exact Function.Surjective.divisibleBy (Circle.expHom : ℝ → Additive Circle) hExp
        (fun a n ↦ Circle.expHom.map_zsmul n a)
  intro χ
  let χadd : H.toAddSubgroup →ₜ+ Additive Circle :=
    ContinuousMonoidHom.toAdditiveRight (A := Additive H) χ
  have hHadd : IsOpen (H.toAddSubgroup : Set (Additive A)) :=
    hH.preimage continuous_toMul
  obtain ⟨F, hF⟩ := ContinuousAddMonoidHom.exists_extension_of_isOpen
    H.toAddSubgroup hHadd χadd
  refine ⟨(ContinuousMonoidHom.toAdditiveRight (A := Additive A)).symm F, ?_⟩
  apply PontryaginDual.ext
  intro h
  exact congrArg (Additive.toMul : Additive Circle → Circle) (hF (Additive.ofMul h))
