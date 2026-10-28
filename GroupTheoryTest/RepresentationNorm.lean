/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationNorm
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Lifting fixed vectors through a surjective intertwining map

The surjectivity theorem for fixed submodules gives a fixed ambient preimage of a vector
specified by its fixed-vector equations. The value of the restricted map is recovered
through its public coercion formula. For bundled representations on additive commutative
groups, norm naturality recovers the categorical composition law of Mathlib's
`Rep.norm_comm` on the same representations and module structures.
-/

@[expose] public section

open CategoryTheory

universe uR uG uA uB uV

/-- A morphism of bundled representations commutes with the categorical norm. -/
private lemma Rep.norm_comm_of_intertwiningMap
    {R : Type uR} {G : Type uG} [Semiring R] [Group G] [Fintype G]
    {X Y : Rep.{uV} R G} (f : X ⟶ Y) :
    f ≫ Rep.norm Y = Rep.norm X ≫ f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  change (Representation.norm Y.ρ).comp f.hom.toLinearMap =
    f.hom.toLinearMap.comp (Representation.norm X.ρ)
  exact (Representation.IntertwiningMap.norm_comm f.hom).symm

example {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
    [Semiring R] [Group G] [Finite G]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    {rhoA : Representation R G A} {rhoB : Representation R G B}
    (f : Representation.IntertwiningMap rhoA rhoB) (hf : Function.Surjective f)
    (hB : Function.Bijective (fun b : B => (Nat.card G) • b))
    (b : B) (hb : ∀ g : G, rhoB g b = b) :
    ∃ a : A, (∀ g : G, rhoA g a = a) ∧ f a = b := by
  obtain ⟨a, ha⟩ :=
    (@Representation.IntertwiningMap.fixedSubmoduleMap_surjective
      R G A B _ _ _ _ _ _ _ rhoA rhoB f hf hB)
      ⟨b, (Representation.mem_fixedSubmodule rhoB b).2 hb⟩
  refine ⟨(a : A), (Representation.mem_fixedSubmodule rhoA (a : A)).1 a.property, ?_⟩
  simpa only [Representation.IntertwiningMap.fixedSubmoduleMap_apply] using
    congrArg (fun c : rhoB.fixedSubmodule => (c : B)) ha
