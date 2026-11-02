/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Coordinates on continuous homomorphisms from free abelian groups

For a discrete free abelian group, evaluation on the generators is an additive
homeomorphism from its continuous additive homomorphisms to the product of the target
indexed by the generators. The inverse extends generator values using
`FreeAbelianGroup.lift`.

The source retains its supplied discrete topology. The homomorphism space carries the
compact-open topology, and the coordinate space carries the product topology.

## References

This construction reuses Mathlib's free abelian universal property, `lift` and `liftAddEquiv`
from `Mathlib.GroupTheory.FreeAbelianGroup`, its discrete-source continuous-map
homeomorphism from `Mathlib.Topology.CompactOpen`, and its compact-open
continuous-homomorphism topology from `Mathlib.Topology.Algebra.Group.CompactOpen`.
-/

@[expose] public section

universe u v w z

namespace ContinuousAddMonoidHom

variable (I : Type u) (A : Type v) [AddCommGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A]

private theorem continuous_lift_eval (x : FreeAbelianGroup I) :
    Continuous (fun c : I → A => FreeAbelianGroup.lift c x) := by
  induction x using FreeAbelianGroup.induction_on with
  | zero =>
      simpa only [map_zero] using
        (continuous_const : Continuous (fun _ : I → A => (0 : A)))
  | of i =>
      simpa only [FreeAbelianGroup.lift_apply_of] using
        (continuous_apply i : Continuous (fun c : I → A => c i))
  | neg i hi =>
      simpa only [map_neg, Pi.neg_def] using hi.neg
  | add x y hx hy =>
      simpa only [map_add, Pi.add_def] using hx.add hy

variable [TopologicalSpace (FreeAbelianGroup I)] [DiscreteTopology (FreeAbelianGroup I)]

/-- Evaluation on the generators identifies continuous additive homomorphisms from a
discrete free abelian group with arbitrary generator values. -/
def freeAbelianGroupEquiv :
    ContinuousAddMonoidHom (FreeAbelianGroup I) A ≃ₜ+ (I → A) where
  toAddEquiv :=
    { toFun := fun φ i => φ (FreeAbelianGroup.of i)
      invFun := fun c =>
        { toAddMonoidHom := FreeAbelianGroup.lift c
          continuous_toFun := continuous_of_discreteTopology }
      left_inv := fun φ => toAddMonoidHom_injective
        ((FreeAbelianGroup.liftAddEquiv (α := I) (G := A)).apply_symm_apply
          φ.toAddMonoidHom)
      right_inv := fun c =>
        (FreeAbelianGroup.liftAddEquiv (α := I) (G := A)).symm_apply_apply c
      map_add' := fun φ ψ =>
        (FreeAbelianGroup.liftAddEquiv (α := I) (G := A)).symm.map_add
          φ.toAddMonoidHom ψ.toAddMonoidHom }
  continuous_toFun := continuous_pi_iff.mpr fun i =>
    continuous_eval_const (FreeAbelianGroup.of i)
  continuous_invFun := by
    -- Discreteness identifies the compact-open function space with all functions.
    -- Continuity must therefore be checked at every group element, not just generators.
    refine ((ContinuousMap.homeoFnOfDiscrete :
      C(FreeAbelianGroup I, A) ≃ₜ (FreeAbelianGroup I → A)).isInducing.comp
        (isInducing_toContinuousMap (FreeAbelianGroup I) A)).continuous_iff.mpr ?_
    exact continuous_pi_iff.mpr (continuous_lift_eval I A)

variable {I A}

/-- The coordinates of a homomorphism are its values on the free generators. -/
@[simp]
theorem freeAbelianGroupEquiv_apply
    (φ : ContinuousAddMonoidHom (FreeAbelianGroup I) A) (i : I) :
    freeAbelianGroupEquiv I A φ i = φ (FreeAbelianGroup.of i) := rfl

/-- The inverse coordinate map has underlying additive homomorphism `FreeAbelianGroup.lift`. -/
theorem freeAbelianGroupEquiv_symm_toAddMonoidHom (c : I → A) :
    ((freeAbelianGroupEquiv I A).symm c).toAddMonoidHom = FreeAbelianGroup.lift c := rfl

/-- As a function, the inverse coordinate map is the free abelian lift. -/
@[simp]
theorem coe_freeAbelianGroupEquiv_symm (c : I → A) :
    ⇑((freeAbelianGroupEquiv I A).symm c) = FreeAbelianGroup.lift c := rfl

/-- Evaluation of the inverse coordinate map agrees with the free abelian lift. -/
@[simp]
theorem freeAbelianGroupEquiv_symm_apply (c : I → A) (x : FreeAbelianGroup I) :
    (freeAbelianGroupEquiv I A).symm c x = FreeAbelianGroup.lift c x := rfl

/-- The inverse coordinate map takes each generator to its prescribed value. -/
theorem freeAbelianGroupEquiv_symm_apply_of (c : I → A) (i : I) :
    (freeAbelianGroupEquiv I A).symm c (FreeAbelianGroup.of i) = c i :=
  FreeAbelianGroup.lift_apply_of c i

omit [IsTopologicalAddGroup A] [DiscreteTopology (FreeAbelianGroup I)] in
/-- Continuous additive homomorphisms from a free abelian group agree if they agree on
its generators. -/
@[ext]
theorem freeAbelianGroup_ext
    {φ ψ : ContinuousAddMonoidHom (FreeAbelianGroup I) A}
    (h : ∀ i, φ (FreeAbelianGroup.of i) = ψ (FreeAbelianGroup.of i)) : φ = ψ :=
  toAddMonoidHom_injective (FreeAbelianGroup.lift_ext _ _ h)

/-- Lifting the generator coordinates reconstructs the underlying additive homomorphism. -/
@[simp]
theorem lift_freeAbelianGroupEquiv
    (φ : ContinuousAddMonoidHom (FreeAbelianGroup I) A) :
    FreeAbelianGroup.lift (freeAbelianGroupEquiv I A φ) = φ.toAddMonoidHom :=
  (FreeAbelianGroup.liftAddEquiv (α := I) (G := A)).apply_symm_apply φ.toAddMonoidHom

/-- A family of continuous additive homomorphisms from a discrete free abelian group is
continuous precisely when its values on every generator vary continuously. -/
theorem continuous_freeAbelianGroup_iff {X : Type w} [TopologicalSpace X]
    {f : X → ContinuousAddMonoidHom (FreeAbelianGroup I) A} :
    Continuous f ↔ ∀ i, Continuous (fun x => f x (FreeAbelianGroup.of i)) :=
  ((freeAbelianGroupEquiv I A).toHomeomorph.isInducing.continuous_iff (f := f)).trans
    continuous_pi_iff

section Target

variable {B : Type w} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]

/-- Postcomposition acts on the generator coordinates by the same target homomorphism. -/
@[simp]
theorem freeAbelianGroupEquiv_comp (g : ContinuousAddMonoidHom A B)
    (φ : ContinuousAddMonoidHom (FreeAbelianGroup I) A) :
    freeAbelianGroupEquiv I B (g.comp φ) = fun i => g (freeAbelianGroupEquiv I A φ i) := rfl

/-- Extending generator values commutes with continuous additive postcomposition. -/
theorem freeAbelianGroupEquiv_symm_comp (g : ContinuousAddMonoidHom A B) (c : I → A) :
    (freeAbelianGroupEquiv I B).symm (fun i => g (c i)) =
      g.comp ((freeAbelianGroupEquiv I A).symm c) := by
  apply ContinuousAddMonoidHom.ext
  intro x
  exact FreeAbelianGroup.lift_comp_apply x c g.toAddMonoidHom

end Target

/-- Reindexing generator values agrees with evaluation after the induced map of free
abelian groups. -/
theorem freeAbelianGroupEquiv_symm_map {J : Type z}
    [TopologicalSpace (FreeAbelianGroup J)] [DiscreteTopology (FreeAbelianGroup J)]
    (f : I → J) (c : J → A) (x : FreeAbelianGroup I) :
    (freeAbelianGroupEquiv I A).symm (c ∘ f) x =
      (freeAbelianGroupEquiv J A).symm c (FreeAbelianGroup.map f x) :=
  FreeAbelianGroup.lift_comp f c x

end ContinuousAddMonoidHom
