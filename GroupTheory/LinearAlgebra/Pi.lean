/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Logic.Equiv.Basic

/-!
# Indexed products of submodules

`Submodule.piEquiv` identifies the submodule of functions whose coordinates belong to
`p i` with the dependent product of the submodule types `p i`. Its coordinate formulas
and inclusion identity use the original function and submodule module structures.
There is no finiteness or nonemptiness assumption on the index type.

The underlying equivalence is Mathlib's `Equiv.subtypeEquivRight` followed by
`Equiv.subtypePiEquivPi`; only the linear-compatibility fields are added. The
representation-specific use is in `GroupTheory.RepresentationPi`.

## References

This linear enrichment uses Mathlib's subtype equivalences in `Mathlib.Logic.Equiv.Basic`,
its `Submodule.pi`, `Submodule.mem_pi` and linear-product API in
`Mathlib.LinearAlgebra.Pi` (Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
and Eric Wieser), and its submodule inclusions in
`Mathlib.Algebra.Module.Submodule.LinearMap` (Mario Carneiro). The dependent-function
module instances in `Mathlib.Algebra.Module.Pi` are by Simon Hudon and Patrick Massot.
-/

@[expose] public section

universe uR uI uM uN

namespace LinearMap

variable {R : Type uR} [Semiring R] {I : Type uI} {M : I → Type uM} {N : I → Type uN}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- Evaluating a pointwise linear map applies the given map to the corresponding coordinate. -/
theorem piMap_apply (f : ∀ i, M i →ₗ[R] N i) (x : ∀ i, M i) (i : I) :
    piMap f x i = f i (x i) :=
  congrFun (congrFun (coe_piMap f) x) i

end LinearMap

namespace Submodule

variable {R : Type uR} [Semiring R] {I : Type uI} {M : I → Type uM}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Splitting coordinates identifies a full indexed submodule product with the product
of its submodule types, by linear enrichment of Mathlib's subtype–Pi equivalence. -/
def piEquiv (p : ∀ i, Submodule R (M i)) :
    (pi Set.univ p) ≃ₗ[R] (∀ i, p i) :=
  { (Equiv.subtypeEquivRight (fun x : ∀ i, M i =>
      show x ∈ pi Set.univ p ↔ ∀ i, x i ∈ p i from
        ⟨fun hx i => (mem_pi.mp hx) i (Set.mem_univ i),
          fun hx => mem_pi.mpr (fun i _ => hx i)⟩)).trans
      Equiv.subtypePiEquivPi with
    map_add' := by
      intro x y
      funext i
      apply Subtype.ext
      rfl
    map_smul' := by
      intro r x
      funext i
      apply Subtype.ext
      rfl }

/-- Splitting an indexed submodule product preserves every ambient coordinate. -/
@[simp]
theorem piEquiv_apply (p : ∀ i, Submodule R (M i)) (x : pi Set.univ p) (i : I) :
    (piEquiv p x i : M i) = (x : ∀ i, M i) i := rfl

/-- The inverse splitting assembles the original ambient coordinates. -/
@[simp]
theorem coe_piEquiv_symm_apply (p : ∀ i, Submodule R (M i)) (y : ∀ i, p i) (i : I) :
    ((piEquiv p).symm y : ∀ i, M i) i = (y i : M i) := rfl

/-- The indexed splitting commutes with the inclusions into the original function module. -/
theorem subtype_piMap_comp_piEquiv (p : ∀ i, Submodule R (M i)) :
    (LinearMap.piMap (fun i => (p i).subtype)).comp (piEquiv p).toLinearMap =
      (pi Set.univ p).subtype := by
  apply LinearMap.ext
  intro x
  funext i
  simpa only [LinearMap.comp_apply, LinearMap.piMap_apply, LinearEquiv.coe_coe,
    subtype_apply] using piEquiv_apply p x i

end Submodule
