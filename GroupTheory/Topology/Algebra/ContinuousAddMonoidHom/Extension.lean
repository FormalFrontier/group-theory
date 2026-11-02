/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.HomContinuity
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Extending continuous additive homomorphisms from open subgroups

Every continuous additive homomorphism from an open subgroup of an abelian group to a divisible
abelian group extends to the whole group. Both groups carry their given topologies, and only
separate continuity of addition is required. The subgroup carries its induced topology.

Restriction is a function between continuous-homomorphism types. Its surjectivity does not assert
uniqueness of extensions or provide a continuous, additive or natural family of chosen extensions.
No additive-group structure on the continuous-homomorphism types is required.

## Implementation notes

The algebraic extension uses the canonical integer actions and the supplied `DivisibleBy D ℤ`
data. Continuity follows from the open-subset criterion for homomorphisms with separately
continuous addition. No continuity of negation, joint addition, or scalar multiplication is needed.

## References

* Jujian Zhang's formalization of divisible groups and Baer's criterion in Mathlib:
  `Module.Baer.of_divisible` and `Module.Baer.extension_property_addMonoidHom`.
* Mathlib's `ContinuousAddMonoidHom.comp` and subgroup inclusion supply restriction.
* `GroupTheory.Topology.HomContinuity` supplies the separate-continuity open-subset criterion.
-/

@[expose] public section

universe u v

namespace ContinuousAddMonoidHom

variable {A : Type u} {D : Type v}

section Restrict

variable [AddGroup A] [TopologicalSpace A] [AddMonoid D] [TopologicalSpace D]

/-- Restriction of a continuous additive homomorphism to a subgroup with its induced topology. -/
def restrict (f : A →ₜ+ D) (H : AddSubgroup A) : H →ₜ+ D :=
  f.comp ⟨H.subtype, continuous_subtype_val⟩

/-- Restriction evaluates the original homomorphism at the subgroup inclusion. -/
@[simp]
theorem restrict_apply (f : A →ₜ+ D) (H : AddSubgroup A) (h : H) :
    f.restrict H h = f (h : A) := rfl

/-- Forgetting continuity identifies restriction with composition by the subgroup inclusion. -/
@[simp]
theorem restrict_toAddMonoidHom (f : A →ₜ+ D) (H : AddSubgroup A) :
    (f.restrict H : H →+ D) = (f : A →+ D).comp H.subtype := rfl

end Restrict

section Extension

variable [AddCommGroup A] [TopologicalSpace A] [SeparatelyContinuousAdd A]
  [AddCommGroup D] [TopologicalSpace D] [SeparatelyContinuousAdd D] [DivisibleBy D ℤ]

/-- A continuous additive homomorphism from an open subgroup of an abelian group to a divisible
abelian group extends continuously to the whole group. Only separate continuity of addition in
both groups is needed. The algebraic extension is supplied by Mathlib's Baer criterion. -/
theorem exists_extension_of_isOpen (H : AddSubgroup A) (hH : IsOpen (H : Set A))
    (f : H →ₜ+ D) : ∃ F : A →ₜ+ D, ∀ h : H, F (h : A) = f h := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible D).extension_property_addMonoidHom
    H.subtype Subtype.val_injective f.toAddMonoidHom
  have hgH : Continuous (fun h : H ↦ g (h : A)) := by
    have hgf : (fun h : H ↦ g (h : A)) = (f : H → D) :=
      funext fun h ↦ DFunLike.congr_fun hg h
    rw [hgf]
    exact f.continuous_toFun
  refine ⟨⟨g, ?_⟩, fun h ↦ DFunLike.congr_fun hg h⟩
  exact (continuous_iff_continuous_domRestrict_of_isOpen_of_zero_mem
    (F := A →+ D) (U := (H : Set A)) g hH H.zero_mem).2 hgH

/-- Restriction to an open subgroup is surjective for continuous additive homomorphisms into a
divisible abelian group, assuming separately continuous addition in the source and target. -/
theorem restrict_surjective_of_isOpen (H : AddSubgroup A) (hH : IsOpen (H : Set A)) :
    Function.Surjective (fun F : A →ₜ+ D ↦ F.restrict H) := by
  intro f
  obtain ⟨F, hF⟩ := exists_extension_of_isOpen H hH f
  exact ⟨F, ContinuousAddMonoidHom.ext hF⟩

/-- The range of restriction to an open subgroup is the entire continuous-homomorphism type when
the target is divisible and addition is separately continuous in both groups. -/
theorem range_restrict_of_isOpen (H : AddSubgroup A) (hH : IsOpen (H : Set A)) :
    Set.range (fun F : A →ₜ+ D ↦ F.restrict H) = Set.univ :=
  Set.range_eq_univ.mpr (restrict_surjective_of_isOpen H hH)

end Extension

end ContinuousAddMonoidHom
