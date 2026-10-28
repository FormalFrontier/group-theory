/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Naturality of the norm on representations

An intertwining linear map commutes with the sum of the group operators.
The coefficient modules need only be additive commutative monoids, and their
carriers may belong to independent universes.

## References

* Mathlib's `Representation.norm` and `Representation.IntertwiningMap`.
* Mathlib's `Rep.norm_comm`, whose categorical statement uses additive groups
  and a common coefficient-carrier universe.
-/

@[expose] public section

universe uR uG uA uB

namespace Representation.IntertwiningMap

variable {R : Type uR} {G : Type uG} {A : Type uA} {B : Type uB}
  [Semiring R] [Group G] [Fintype G]
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  {rhoA : Representation R G A} {rhoB : Representation R G B}

/-- An intertwining linear map commutes with the norm endomorphisms. -/
theorem norm_comm (f : IntertwiningMap rhoA rhoB) :
    f.toLinearMap.comp (Representation.norm rhoA) =
      (Representation.norm rhoB).comp f.toLinearMap := by
  classical
  ext a
  simp only [Representation.norm, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun g _ ↦
    Representation.IntertwiningMap.isIntertwining rhoA rhoB f g a

/-- An intertwiner sends a norm value to the norm of the image. -/
theorem norm_comm_apply (f : IntertwiningMap rhoA rhoB) (a : A) :
    f (Representation.norm rhoA a) = Representation.norm rhoB (f a) := by
  exact congrArg (fun l : A →ₗ[R] B ↦ l a) (norm_comm f)

end Representation.IntertwiningMap
