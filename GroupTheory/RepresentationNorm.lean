/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants
public import GroupTheory.RepresentationNormNaturality
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Norms and surjections on fixed vectors

For representations of a finite group over a semiring, every value of the target norm
has a fixed preimage under a surjective intertwining map. Thus the map on fixed submodules
is surjective whenever the target norm is onto the fixed submodule.

Surjectivity of multiplication by the group order on the target fixed submodule suffices.
In particular, bijectivity of this multiplication on the ambient target suffices: the
unique root of a fixed vector is fixed. None of these statements requires additive
inverses, cancellation, or divisibility of the source module.

## References

The proofs use Mathlib's `Representation.norm` and its fixed-value identities, formalized
by Antoine Labelle in `Mathlib.RepresentationTheory.Basic`, and the intertwining-map API
of Stepan Nesterov and Edison Xie in `Mathlib.RepresentationTheory.Intertwining`.
-/

@[expose] public section

universe uR uG uA uB

namespace Representation

/-- The norm of a fixed vector is multiplication by the order of the group. -/
@[simp]
theorem norm_apply_coe_fixedSubmodule
    {R : Type uR} {G : Type uG} {A : Type uA}
    [Semiring R] [Group G] [Fintype G] [AddCommMonoid A] [Module R A]
    (rhoA : Representation R G A) (a : rhoA.fixedSubmodule) :
    norm rhoA (a : A) = Fintype.card G • (a : A) := by
  classical
  simp only [norm, LinearMap.sum_apply, apply_coe_fixedSubmodule,
    Finset.sum_const, Finset.card_univ]

namespace IntertwiningMap

/-- Every value of the target norm has a fixed preimage under a surjective
intertwining map. -/
theorem exists_fixed_preimage_norm
    {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Fintype G]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB)
    (hf : Function.Surjective f) (b : B) :
    ∃ a : rhoA.fixedSubmodule, f a = Representation.norm rhoB b := by
  classical
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨⟨norm rhoA a, ?_⟩, ?_⟩
  · exact (mem_fixedSubmodule rhoA (norm rhoA a)).2 (fun g => self_norm_apply rhoA g a)
  · exact f.norm_comm_apply a

/-- A surjective intertwining map is surjective on fixed submodules if every fixed
target vector is a value of the target norm. -/
theorem fixedSubmoduleMap_surjective_of_norm_surjective
    {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Fintype G]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB)
    (hf : Function.Surjective f)
    (hB : ∀ b : rhoB.fixedSubmodule,
      ∃ b0 : B, Representation.norm rhoB b0 = (b : B)) :
    Function.Surjective f.fixedSubmoduleMap := by
  intro b
  obtain ⟨b0, hb0⟩ := hB b
  obtain ⟨a, ha⟩ := f.exists_fixed_preimage_norm hf b0
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa only [fixedSubmoduleMap_apply] using ha.trans hb0

/-- Surjectivity of multiplication by the group order on the target fixed submodule
makes the restriction of a surjective intertwining map surjective. -/
theorem fixedSubmoduleMap_surjective_of_nsmul_surjective
    {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Finite G]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB)
    (hf : Function.Surjective f)
    (hB : Function.Surjective
      (fun b : rhoB.fixedSubmodule => (Nat.card G) • b)) :
    Function.Surjective f.fixedSubmoduleMap := by
  let := Fintype.ofFinite G
  apply f.fixedSubmoduleMap_surjective_of_norm_surjective hf
  intro b
  obtain ⟨c, hc⟩ := hB b
  refine ⟨(c : B), ?_⟩
  calc
    norm rhoB (c : B) = Fintype.card G • (c : B) :=
      norm_apply_coe_fixedSubmodule rhoB c
    _ = (b : B) := by
      simpa only [Submodule.coe_smul_of_tower, Fintype.card_eq_nat_card] using
        congrArg (fun d : rhoB.fixedSubmodule => (d : B)) hc

/-- A surjective intertwining map is surjective on fixed submodules when multiplication
by the group order is bijective on the ambient target module. -/
theorem fixedSubmoduleMap_surjective
    {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Finite G]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB)
    (hf : Function.Surjective f)
    (hB : Function.Bijective (fun b : B => (Nat.card G) • b)) :
    Function.Surjective f.fixedSubmoduleMap := by
  apply f.fixedSubmoduleMap_surjective_of_nsmul_surjective hf
  intro b
  obtain ⟨c, hc⟩ := hB.2 (b : B)
  have hc_fixed : c ∈ rhoB.fixedSubmodule := by
    apply (mem_fixedSubmodule rhoB c).2
    intro g
    apply hB.1
    calc
      (Nat.card G) • rhoB g c = rhoB g ((Nat.card G) • c) :=
        (map_nsmul (rhoB g) (Nat.card G) c).symm
      _ = rhoB g (b : B) := congrArg (rhoB g) hc
      _ = (b : B) := apply_coe_fixedSubmodule rhoB g b
      _ = (Nat.card G) • c := hc.symm
  refine ⟨⟨c, hc_fixed⟩, ?_⟩
  apply Subtype.ext
  simpa only [Submodule.coe_smul_of_tower] using hc

/-- If the group order is a unit in the scalar semiring, a surjective intertwining map
is surjective on fixed submodules. -/
theorem fixedSubmoduleMap_surjective_of_isUnit
    {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Finite G]
    [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB)
    (hf : Function.Surjective f) (hR : IsUnit (Nat.card G : R)) :
    Function.Surjective f.fixedSubmoduleMap := by
  apply f.fixedSubmoduleMap_surjective hf
  simpa only [Nat.cast_smul_eq_nsmul] using
    (hR.smul_bijective : Function.Bijective (fun b : B => (Nat.card G : R) • b))

end IntertwiningMap

end Representation
