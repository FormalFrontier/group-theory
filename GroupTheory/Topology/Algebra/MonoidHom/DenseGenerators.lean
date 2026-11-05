/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Uniqueness from dense generators

Continuous monoid homomorphisms from a group with any topology into a monoid with a Hausdorff
topology are determined by their values on a set whose algebraically generated subgroup is dense.
No continuity of the operations is assumed.

The proof reuses Mathlib's algebraic extension and uniqueness on dense sets.
-/

public section

namespace MonoidHomClass

variable {G : Type*} {M : Type*} {F : Type*} [Group G] [Monoid M]
  [TopologicalSpace G] [TopologicalSpace M] [T2Space M] [FunLike F G M] [MonoidHomClass F G M]

/-- Continuous monoid homomorphisms agreeing on a densely generating set are equal. -/
theorem eq_of_eqOn_dense_closure {s : Set G} (hs : Dense (Subgroup.closure s : Set G))
    {f g : F} (hf : Continuous f) (hg : Continuous g) (h : Set.EqOn f g s) : f = g :=
  DFunLike.ext' <| Continuous.ext_on hs hf hg <|
    MonoidHom.eqOn_closure (f := (f : G →* M)) (g := (g : G →* M)) h

end MonoidHomClass
