/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Hom.ContinuousEvalConst
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff

/-!
# Evaluation at free generators

A surjection from a free monoid determines continuous monoid homomorphisms by their
generator values. For a discrete source, these values extend exactly when their
free lift respects all word relations. If the target is Hausdorff and its
multiplication is continuous, generator evaluation is a closed embedding from the
compact-open homomorphism space into the product of copies of the target.

For a finitely generated discrete monoid, the finite-product case gives local
compactness when the target is locally compact. No group structure, commutativity,
or finite presentation is required.
-/

@[expose] public section

universe a b u v w

open Filter Function Topology

namespace Con

/-- The kernel-quotient equivalence of a surjective homomorphism sends a
representative to its image. -/
theorem quotientKerEquivOfSurjective_mk'_eq
    {A : Type a} {B : Type b}
    [MulOneClass A] [MulOneClass B]
    (f : A →* B) (hf : Function.Surjective f) (x : A) :
    Con.quotientKerEquivOfSurjective f hf
      ((Con.ker f).mk' x) = f x := by
  change Con.kerLift f x = f x
  exact Con.kerLift_mk (f := f) x

end Con

namespace FreeMonoid

/-- Evaluation of a fixed free-monoid word is continuous in the generator assignment. -/
theorem continuous_lift_apply
    {S : Type u} {D : Type w}
    [Monoid D] [TopologicalSpace D] [ContinuousMul D]
    (x : FreeMonoid S) :
    Continuous (fun g : S → D => FreeMonoid.lift g x) := by
  simpa only [FreeMonoid.lift_apply] using
    (continuous_list_prod
      (f := fun s (g : S → D) => g s)
      (FreeMonoid.toList x)
      (fun s _ => continuous_apply s))

end FreeMonoid

namespace ContinuousMonoidHom

/-- Evaluation on the images of free generators is continuous in the compact-open topology. -/
theorem continuous_eval_freeMonoid_generators
    {S : Type u} {M : Type v} {D : Type w}
    [Monoid M] [Monoid D]
    [TopologicalSpace M] [TopologicalSpace D]
    (φ : FreeMonoid S →* M) :
    Continuous
      (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) := by
  exact continuous_pi fun s =>
    continuous_eval_const (φ (FreeMonoid.of s))

section GeneratorEvaluation

variable {S : Type u} {M : Type v} {D : Type w}
variable [Monoid M] [Monoid D]
variable [TopologicalSpace M] [TopologicalSpace D]
variable (φ : FreeMonoid S →* M)

/-- Generator values determine a continuous monoid homomorphism along a
surjective free-monoid presentation. -/
theorem injective_eval_freeMonoid_generators
    (hφ : Function.Surjective φ) :
    Function.Injective
      (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) := by
  intro h k hhk
  have hcomp : h.toMonoidHom.comp φ = k.toMonoidHom.comp φ := by
    calc
      h.toMonoidHom.comp φ =
          FreeMonoid.lift (fun s : S => h (φ (FreeMonoid.of s))) :=
        (FreeMonoid.lift_restrict (h.toMonoidHom.comp φ)).symm
      _ = FreeMonoid.lift (fun s : S => k (φ (FreeMonoid.of s))) :=
        congrArg (fun g : S → D => FreeMonoid.lift g) hhk
      _ = k.toMonoidHom.comp φ :=
        FreeMonoid.lift_restrict (k.toMonoidHom.comp φ)
  apply ContinuousMonoidHom.ext
  intro m
  obtain ⟨x, rfl⟩ := hφ m
  exact congrArg (fun f : FreeMonoid S →* D => f x) hcomp

/-- For a discrete source, generator values extend to a continuous monoid
homomorphism exactly when their free lift respects every word relation. -/
theorem mem_range_eval_freeMonoid_generators_iff
    [DiscreteTopology M]
    (hφ : Function.Surjective φ) (g : S → D) :
    g ∈ Set.range
      (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) ↔
      ∀ x y : FreeMonoid S, φ x = φ y →
        FreeMonoid.lift g x = FreeMonoid.lift g y := by
  constructor
  · rintro ⟨h, rfl⟩ x y hxy
    have hword :
        FreeMonoid.lift (fun s : S => h (φ (FreeMonoid.of s))) =
          h.toMonoidHom.comp φ :=
      FreeMonoid.lift_restrict (h.toMonoidHom.comp φ)
    calc
      FreeMonoid.lift (fun s : S => h (φ (FreeMonoid.of s))) x = h (φ x) :=
        congrArg (fun f : FreeMonoid S →* D => f x) hword
      _ = h (φ y) := congrArg h hxy
      _ = FreeMonoid.lift (fun s : S => h (φ (FreeMonoid.of s))) y :=
        (congrArg (fun f : FreeMonoid S →* D => f y) hword).symm
  · intro hg
    have H : Con.ker φ ≤ Con.ker (FreeMonoid.lift g) := by
      intro x y hxy
      exact Con.ker_apply.mpr (hg x y (Con.ker_apply.mp hxy))
    let e := Con.quotientKerEquivOfSurjective φ hφ
    let d := (Con.ker φ).lift (FreeMonoid.lift g) H
    let f : M →* D := d.comp e.symm.toMonoidHom
    have hf (x : FreeMonoid S) : f (φ x) = FreeMonoid.lift g x := by
      change d (e.symm (φ x)) = FreeMonoid.lift g x
      have hx : e ((Con.ker φ).mk' x) = φ x :=
        Con.quotientKerEquivOfSurjective_mk'_eq φ hφ x
      rw [← hx, e.symm_apply_apply]
      exact Con.lift_mk' H x
    let h : ContinuousMonoidHom M D :=
      { toMonoidHom := f
        continuous_toFun := continuous_of_discreteTopology }
    refine ⟨h, ?_⟩
    funext s
    change f (φ (FreeMonoid.of s)) = g s
    rw [hf, FreeMonoid.lift_eval_of]

/-- Generator evaluation identifies the compact-open space of homomorphisms from a
 discrete monoid with a closed subspace of the space of generator assignments. The
 alphabet may be arbitrary; the image is cut out by all equal-value word pairs. -/
theorem isClosedEmbedding_eval_freeMonoid_generators
    [DiscreteTopology M] [ContinuousMul D] [T2Space D]
    (hφ : Function.Surjective φ) :
    Topology.IsClosedEmbedding
      (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) := by
  have hlift (h : ContinuousMonoidHom M D) (x : FreeMonoid S) :
      FreeMonoid.lift (fun s : S => h (φ (FreeMonoid.of s))) x = h (φ x) := by
    exact congrArg (fun f : FreeMonoid S →* D => f x)
      (FreeMonoid.lift_restrict (h.toMonoidHom.comp φ))
  -- The discrete-source homeomorphism has the original function as its forward map.
  have hfull : Topology.IsInducing
      (fun h : ContinuousMonoidHom M D => fun m : M => h m) := by
    exact (ContinuousMap.homeoFnOfDiscrete (X := M) (Y := D)).isInducing.comp
      (ContinuousMonoidHom.isInducing_toContinuousMap M D)
  have hind : Topology.IsInducing
      (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) := by
    apply Topology.isInducing_iff_nhds.mpr
    intro h
    refine le_antisymm ?_ ?_
    · exact Filter.tendsto_iff_comap.mp
        ((continuous_eval_freeMonoid_generators φ).tendsto h)
    · rw [(Topology.isInducing_iff_nhds.mp hfull) h]
      apply Filter.tendsto_iff_comap.mp
      apply tendsto_pi_nhds.mpr
      intro m
      -- Choose a word for this one evaluation only, inside the proposition proof.
      obtain ⟨x, rfl⟩ := hφ m
      simpa only [Function.comp_def, hlift] using
        ((FreeMonoid.continuous_lift_apply (D := D) x).tendsto
          (fun s : S => h (φ (FreeMonoid.of s)))).comp
          (Filter.tendsto_comap
            (f := fun k : ContinuousMonoidHom M D =>
              fun s : S => k (φ (FreeMonoid.of s)))
            (x := 𝓝 (fun s : S => h (φ (FreeMonoid.of s)))))
  refine
    { toIsEmbedding :=
        { toIsInducing := hind
          injective := injective_eval_freeMonoid_generators φ hφ }
      isClosed_range := ?_ }
  have hrange :
      Set.range (fun h : ContinuousMonoidHom M D =>
        fun s : S => h (φ (FreeMonoid.of s))) =
      ⋂ x : FreeMonoid S, ⋂ y : FreeMonoid S, ⋂ (_ : φ x = φ y),
        {g : S → D | FreeMonoid.lift g x = FreeMonoid.lift g y} := by
    ext g
    simp only [Set.mem_iInter]
    exact mem_range_eval_freeMonoid_generators_iff φ hφ g
  rw [hrange]
  exact isClosed_iInter (fun x =>
    isClosed_iInter (fun y =>
      isClosed_iInter (fun _ =>
        isClosed_eq (FreeMonoid.continuous_lift_apply (D := D) x)
          (FreeMonoid.continuous_lift_apply (D := D) y))))

end GeneratorEvaluation

/-- The compact-open space of continuous homomorphisms from a finitely generated
 discrete monoid into a locally compact Hausdorff monoid with continuous
 multiplication is locally compact. -/
theorem locallyCompactSpace_of_monoid_fg
    {M : Type v} {D : Type w}
    [Monoid M] [Monoid D]
    [TopologicalSpace M] [TopologicalSpace D]
    [Monoid.FG M] [DiscreteTopology M]
    [ContinuousMul D] [T2Space D] [LocallyCompactSpace D] :
    LocallyCompactSpace (ContinuousMonoidHom M D) := by
  obtain ⟨S, hS, φ, hφ⟩ :=
    Monoid.fg_iff_exists_freeMonoid_hom_surjective.mp
      (show Monoid.FG M from inferInstance)
  let _ : Finite S :=
    (finite_iff_nonempty_fintype S).mpr (Set.finite_def.mp hS)
  exact (isClosedEmbedding_eval_freeMonoid_generators φ hφ).locallyCompactSpace

end ContinuousMonoidHom
