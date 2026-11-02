/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.ContinuousOn

/-!
# Continuity of homomorphisms from groups with separately continuous multiplication

A multiplication-preserving map from a group with separately continuous multiplication to a type
with separately continuous multiplication is continuous if it is continuous at the identity.
The target needs neither an identity nor associativity. The proof uses fixed left translations
and cancellation in the source, not continuity of the inversion function.

The additive versions apply to addition-preserving maps from additive groups, including maps
represented by `AddMonoidHomClass`. Continuity can also be tested on any open set containing the
identity, or on its restriction with the induced subtype topology; this set needs no algebraic
closure properties.

## References

* Mathlib's `continuous_of_continuousAt_one` in
  `Mathlib.Topology.Algebra.Group.Neighborhood` is the topological-group continuity criterion
  generalized here. `continuous_iff_continuousAt_one` records the specialization to its hypotheses.
* Mathlib's `MulHomClass`, `AddHomClass` and `FunLike` provide the homomorphism interface;
  `SeparatelyContinuousMul` and `SeparatelyContinuousAdd` provide fixed-translation continuity.
* The open-set criteria use Mathlib's `IsOpen.continuousOn_iff` and
  `continuousOn_iff_continuous_domRestrict`.
-/

@[expose] public section

universe u v w

variable {G : Type u} {H : Type v} {F : Type w}

section SeparatelyContinuousMul

variable [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [Mul H] [TopologicalSpace H] [SeparatelyContinuousMul H]
  [FunLike F G H] [MulHomClass F G H]

/-- A multiplication-preserving map from a group with separately continuous multiplication is
continuous if it is continuous at the identity. The target only needs multiplication and its
separate continuity. This generalizes Mathlib's `continuous_of_continuousAt_one`. -/
@[to_additive
  /-- An addition-preserving map from an additive group with separately continuous addition is
  continuous if it is continuous at zero. The target only needs addition and its separate
  continuity. This generalizes Mathlib's `continuous_of_continuousAt_zero`. -/]
theorem continuous_of_continuousAt_one_of_separatelyContinuousMul (f : F)
    (hf : ContinuousAt f 1) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have htranslate : ContinuousAt (fun y : G ↦ f (x⁻¹ * y)) x :=
    hf.comp_of_eq (continuous_const_mul x⁻¹).continuousAt (inv_mul_cancel x)
  simpa only [← map_mul, mul_inv_cancel_left] using htranslate.const_mul (f x)

/-- For multiplication-preserving maps from groups with separately continuous multiplication,
continuity is equivalent to continuity at the identity. -/
@[to_additive
  /-- For addition-preserving maps from additive groups with separately continuous addition,
  continuity is equivalent to continuity at zero. -/]
theorem continuous_iff_continuousAt_one_of_separatelyContinuousMul (f : F) :
    Continuous f ↔ ContinuousAt f 1 :=
  ⟨fun hf ↦ hf.continuousAt, continuous_of_continuousAt_one_of_separatelyContinuousMul f⟩

/-- Continuity of a multiplication-preserving map can be tested on an open set containing the
identity. The open set need not be a subgroup. -/
@[to_additive
  /-- Continuity of an addition-preserving map can be tested on an open set containing zero.
  The open set need not be an additive subgroup. -/]
theorem continuous_iff_continuousOn_of_isOpen_of_one_mem (f : F) {U : Set G}
    (hU : IsOpen U) (h1 : 1 ∈ U) : Continuous f ↔ ContinuousOn f U := by
  constructor
  · intro hf
    apply hU.continuousOn_iff.2
    intro x hx
    exact hf.continuousAt
  · intro hf
    exact continuous_of_continuousAt_one_of_separatelyContinuousMul f
      (hU.continuousOn_iff.1 hf h1)

/-- Continuity of a multiplication-preserving map is equivalent to continuity of its restriction
to an open set containing the identity, equipped with its induced subtype topology. -/
@[to_additive
  /-- Continuity of an addition-preserving map is equivalent to continuity of its restriction
  to an open set containing zero, equipped with its induced subtype topology. -/]
theorem continuous_iff_continuous_domRestrict_of_isOpen_of_one_mem (f : F) {U : Set G}
    (hU : IsOpen U) (h1 : 1 ∈ U) :
    Continuous f ↔ Continuous (fun x : U ↦ f (x : G)) :=
  (continuous_iff_continuousOn_of_isOpen_of_one_mem f hU h1).trans
    continuousOn_iff_continuous_domRestrict

end SeparatelyContinuousMul

section IsTopologicalGroup

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulOneClass H] [TopologicalSpace H] [ContinuousMul H]
  [FunLike F G H] [MonoidHomClass F G H]

/-- Under the hypotheses of Mathlib's `continuous_of_continuousAt_one`, the criterion for
separately continuous multiplication specializes to the same function and topologies. The reverse
implication is Mathlib's continuity-at-identity theorem. -/
@[to_additive
  /-- Under the hypotheses of Mathlib's `continuous_of_continuousAt_zero`, the criterion for
  separately continuous addition specializes to the same function and topologies. The reverse
  implication is Mathlib's continuity-at-zero theorem. -/]
theorem continuous_iff_continuousAt_one (f : F) : Continuous f ↔ ContinuousAt f 1 :=
  ⟨(continuous_iff_continuousAt_one_of_separatelyContinuousMul f).mp,
    continuous_of_continuousAt_one f⟩

end IsTopologicalGroup
