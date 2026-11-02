/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.CompactOpen

/-!
# Continuous homomorphisms from a discrete free group

Evaluation on generators identifies the continuous homomorphisms from a discrete free group
with arbitrary families in a topological group. The homomorphism space has its compact-open
topology and the family space has its product topology. No topology on the generating type is
needed, and the target group need not be commutative.

The inverse retains `FreeGroup.lift` as its underlying homomorphism. Continuity of evaluation
at every word follows by free-group induction, preserving the order of multiplication.
Consequently, a family of continuous homomorphisms is continuous precisely when its generator
coordinates are continuous.

The discrete-source hypothesis is essential: an indiscrete free group can have algebraic lifts
to a discrete group that are not continuous. In contrast, generator extensionality below needs
only a monoid target and places no discreteness requirement on the source.

## References

This construction uses Mathlib's universal lift in `Mathlib/GroupTheory/FreeGroup/Basic.lean`
(Kenny Lau), its compact-open homomorphism APIs in
`Mathlib/Topology/Algebra/Group/CompactOpen.lean` (Thomas Browning and Nailin Guan), and its
discrete continuous-map homeomorphism in `Mathlib/Topology/CompactOpen.lean` (Reid Barton).
The function-coercion identifications use Mathlib's homomorphism-class APIs in
`Mathlib/Algebra/Group/Hom/Defs.lean` and continuous-map APIs in
`Mathlib/Topology/ContinuousMap/Defs.lean`.
-/

@[expose] public section

open scoped Topology

universe u v w

namespace FreeGroup

variable {I : Type u} {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation of the universal lift at any free-group word is continuous in the generator
values. This does not require a topology on the free group or on its generating type. -/
theorem continuous_lift_apply (x : FreeGroup I) :
    Continuous (fun c : I → G => FreeGroup.lift c x) := by
  refine FreeGroup.induction_on x ?_ (fun i => ?_) (fun i hi => ?_) (fun x y hx hy => ?_)
  · simpa using
      (continuous_const : Continuous (fun _ : I → G => (1 : G)))
  · simpa only [FreeGroup.lift_apply_of] using
      (continuous_apply i : Continuous (fun c : I → G => c i))
  · simpa only [_root_.map_inv, Pi.inv_def] using hi.inv
  · simpa only [_root_.map_mul, Pi.mul_def] using hx.mul hy

end FreeGroup

namespace ContinuousMonoidHom

section FunctionCoercions

variable {A : Type u} {B : Type v} [Monoid A] [Monoid B]
  [TopologicalSpace A] [TopologicalSpace B]

/-- The inherited function of a continuous homomorphism agrees with its function coercion. -/
theorem toFun_eq_coe (f : ContinuousMonoidHom A B) : f.toFun = (f : A → B) := rfl

/-- The function of a continuous homomorphism constructed from a monoid homomorphism is
its underlying function. -/
@[simp]
theorem coe_mk (f : A →* B) (hf : Continuous f.toFun) :
    ⇑({ toMonoidHom := f, continuous_toFun := hf } : ContinuousMonoidHom A B) =
      (f : A → B) := rfl

end FunctionCoercions

section Extensionality

variable {I : Type u} {M : Type v} [Monoid M]
  [TopologicalSpace (FreeGroup I)] [TopologicalSpace M]

/-- Continuous homomorphisms from a free group agree if they agree on generators.
The target may be any monoid, and the source topology need not be discrete. -/
@[ext]
theorem freeGroup_ext {φ ψ : ContinuousMonoidHom (FreeGroup I) M}
    (h : ∀ i, φ (FreeGroup.of i) = ψ (FreeGroup.of i)) : φ = ψ :=
  toMonoidHom_injective (FreeGroup.ext_hom φ.toMonoidHom ψ.toMonoidHom h)

end Extensionality

section Reconstruction

variable {I : Type u} {G : Type v} [Group G]
  [TopologicalSpace (FreeGroup I)] [TopologicalSpace G]

/-- Lifting the generator values of a continuous homomorphism recovers its underlying
homomorphism, independently of any discreteness or topological-group assumptions. -/
@[simp]
theorem freeGroup_lift_eval (φ : ContinuousMonoidHom (FreeGroup I) G) :
    FreeGroup.lift (fun i => φ (FreeGroup.of i)) = φ.toMonoidHom :=
  FreeGroup.lift.right_inv φ.toMonoidHom

end Reconstruction

section TopologicalGroup

variable {I : Type u} {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace (FreeGroup I)] [DiscreteTopology (FreeGroup I)]

omit [IsTopologicalGroup G] in
private theorem continuous_iff_freeGroup_eval {X : Type w} [TopologicalSpace X]
    (f : X → ContinuousMonoidHom (FreeGroup I) G) :
    Continuous f ↔ ∀ x, Continuous (fun t => f t x) := by
  have hi := (ContinuousMap.homeoFnOfDiscrete (X := FreeGroup I) (Y := G)).isInducing.comp
    (isInducing_toContinuousMap (FreeGroup I) G)
  simpa [Function.comp_def] using
    (hi.continuous_iff (f := f)).trans continuous_pi_iff

/-- A family of continuous homomorphisms from a discrete free group is continuous for the
compact-open topology if and only if its values on each generator vary continuously. -/
theorem continuous_freeGroup_iff {X : Type w} [TopologicalSpace X]
    (f : X → ContinuousMonoidHom (FreeGroup I) G) :
    Continuous f ↔ ∀ i, Continuous (fun t => f t (FreeGroup.of i)) := by
  constructor
  · intro hf i
    exact (continuous_eval_const (FreeGroup.of i)).comp hf
  · intro hf
    apply (continuous_iff_freeGroup_eval f).2
    intro x
    simpa [Function.comp_def] using
      (FreeGroup.continuous_lift_apply (G := G) x).comp (continuous_pi hf)

variable (I G)

/-- Evaluation on generators is a homeomorphism from continuous homomorphisms out of a
discrete free group to arbitrary generator values in a topological group. Its inverse has
underlying homomorphism `FreeGroup.lift`, using the supplied discrete source topology. -/
def freeGroupHomeomorph : (ContinuousMonoidHom (FreeGroup I) G) ≃ₜ (I → G) where
  toFun φ i := φ (FreeGroup.of i)
  invFun c :=
    { toMonoidHom := FreeGroup.lift c
      continuous_toFun := continuous_of_discreteTopology }
  left_inv φ := toMonoidHom_injective (freeGroup_lift_eval φ)
  right_inv c := FreeGroup.lift.left_inv c
  continuous_toFun := continuous_pi fun i => continuous_eval_const (FreeGroup.of i)
  continuous_invFun := (continuous_freeGroup_iff _).2 fun i => by
    simpa using
      (continuous_apply i : Continuous (fun c : I → G => c i))

variable {I G}

/-- The forward homeomorphism evaluates a continuous homomorphism on each generator. -/
@[simp]
theorem freeGroupHomeomorph_apply (φ : ContinuousMonoidHom (FreeGroup I) G) (i : I) :
    freeGroupHomeomorph I G φ i = φ (FreeGroup.of i) := rfl

/-- The inverse homeomorphism stores the universal lift as its underlying homomorphism. -/
theorem freeGroupHomeomorph_symm_toMonoidHom (c : I → G) :
    ((freeGroupHomeomorph I G).symm c).toMonoidHom = FreeGroup.lift c := rfl

/-- As a function, the inverse homeomorphism is the universal lift. -/
@[simp]
theorem coe_freeGroupHomeomorph_symm (c : I → G) :
    ⇑((freeGroupHomeomorph I G).symm c) = (FreeGroup.lift c : FreeGroup I → G) := rfl

/-- Evaluation of the inverse homeomorphism at an arbitrary word. -/
theorem freeGroupHomeomorph_symm_apply (c : I → G) (x : FreeGroup I) :
    (freeGroupHomeomorph I G).symm c x = FreeGroup.lift c x := rfl

/-- The inverse homeomorphism takes the prescribed value on each generator. -/
theorem freeGroupHomeomorph_symm_apply_of (c : I → G) (i : I) :
    (freeGroupHomeomorph I G).symm c (FreeGroup.of i) = c i := by
  rw [freeGroupHomeomorph_symm_apply, FreeGroup.lift_apply_of]

/-- Reconstructing a continuous homomorphism from its generator values recovers it. -/
theorem freeGroupHomeomorph_symm_eval (φ : ContinuousMonoidHom (FreeGroup I) G) :
    (freeGroupHomeomorph I G).symm (fun i => φ (FreeGroup.of i)) = φ :=
  (freeGroupHomeomorph I G).symm_apply_apply φ

section TargetNaturality

variable {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Generator evaluation commutes with composition by a continuous target homomorphism. -/
theorem freeGroupHomeomorph_comp (h : ContinuousMonoidHom G H)
    (φ : ContinuousMonoidHom (FreeGroup I) G) :
    freeGroupHomeomorph I H (h.comp φ) = h ∘ freeGroupHomeomorph I G φ := rfl

/-- Extending generator values commutes with a continuous homomorphism of target groups. -/
theorem freeGroupHomeomorph_symm_comp (h : ContinuousMonoidHom G H) (c : I → G) :
    (freeGroupHomeomorph I H).symm (h ∘ c) =
      h.comp ((freeGroupHomeomorph I G).symm c) := by
  apply freeGroup_ext
  intro i
  simp only [coe_comp, Function.comp_apply, freeGroupHomeomorph_symm_apply_of]

end TargetNaturality

/-- Extending a reindexed generator family is precomposition with the free-group map.
Both free groups retain their supplied discrete topologies. -/
theorem freeGroupHomeomorph_symm_comp_map {J : Type w}
    [TopologicalSpace (FreeGroup J)] [DiscreteTopology (FreeGroup J)]
    (k : I → J) (c : J → G) :
    (freeGroupHomeomorph I G).symm (c ∘ k) =
      ((freeGroupHomeomorph J G).symm c).comp
        { toMonoidHom := FreeGroup.map k
          continuous_toFun := continuous_of_discreteTopology } := by
  have hmap (i : I) :
      ({ toMonoidHom := FreeGroup.map k
         continuous_toFun := continuous_of_discreteTopology } :
        ContinuousMonoidHom (FreeGroup I) (FreeGroup J)) (FreeGroup.of i) =
          FreeGroup.of (k i) := by
    simpa only [coe_mk] using (FreeGroup.map.of (f := k) (x := i))
  apply freeGroup_ext
  intro i
  simp only [coe_comp, Function.comp_apply, hmap, freeGroupHomeomorph_symm_apply_of]

end TopologicalGroup

end ContinuousMonoidHom
