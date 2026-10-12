/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ConstMulAction

/-!
# Clients of fixed-action transport

The clients keep scalar, source and target universes independent. They exercise
full and witness-dot applications, the coercion of equivariant maps, quotient-map
specialization, and the existing fixed-action and observer composition APIs.
Both primitive multiplicative and additive actions are used without action laws
or a topology on the scalar type.

## References

Mathlib supplies the equivariant-map coercions, `map_smul`, `map_vadd`,
`continuous_const_smul`, `continuous_const_vadd` and quotient-map projections.
-/

namespace GroupTheoryTest.Topology.Algebra.ConstMulAction

open _root_.Topology

universe u v w z

section Multiplicative

variable {M : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul M Y]
    [ContinuousConstSMul M X]

private theorem coinducing_full_call (f : X →[M] Y)
    (hf : IsCoinducing (f : X → Y)) (c : M) :
    Continuous (fun y : Y => c • y) := by
  let : ContinuousConstSMul M Y := IsCoinducing.continuousConstSMul f hf
  exact continuous_const_smul c

private theorem coinducing_dot_observer (f : X →[M] Y)
    (hf : IsCoinducing (f : X → Y)) {Z : Type z} [TopologicalSpace Z]
    (h : Y → Z) (hh : Continuous h) (c : M) :
    Continuous (fun y : Y => h (c • y)) := by
  let : ContinuousConstSMul M Y := hf.continuousConstSMul f
  exact hh.comp (continuous_const_smul c)

private theorem quotient_map_client (f : X →[M] Y)
    (hf : IsQuotientMap (f : X → Y)) (c : M) :
    Continuous (fun x : X => c • f x) ∧
      (∀ x : X, f (c • x) = c • f x) := by
  let : ContinuousConstSMul M Y :=
    IsCoinducing.continuousConstSMul f hf.isCoinducing
  exact ⟨(continuous_const_smul c).comp hf.continuous, fun x => map_smul f c x⟩

end Multiplicative

section Additive

variable {M : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [VAdd M X] [VAdd M Y]
    [ContinuousConstVAdd M X]

private theorem coinducing_additive_full_call (f : X →[M] Y)
    (hf : IsCoinducing (f : X → Y)) (c : M) :
    Continuous (fun y : Y => c +ᵥ y) := by
  let : ContinuousConstVAdd M Y := IsCoinducing.continuousConstVAdd f hf
  exact continuous_const_vadd c

private theorem coinducing_additive_dot_observer (f : X →[M] Y)
    (hf : IsCoinducing (f : X → Y)) {Z : Type z} [TopologicalSpace Z]
    (h : Y → Z) (hh : Continuous h) (c : M) :
    Continuous (fun y : Y => h (c +ᵥ y)) := by
  let : ContinuousConstVAdd M Y := hf.continuousConstVAdd f
  exact hh.comp (continuous_const_vadd c)

private theorem additive_quotient_map_client (f : X →[M] Y)
    (hf : IsQuotientMap (f : X → Y)) (c : M) :
    Continuous (fun x : X => c +ᵥ f x) ∧
      (∀ x : X, f (c +ᵥ x) = c +ᵥ f x) := by
  let : ContinuousConstVAdd M Y :=
    IsCoinducing.continuousConstVAdd f hf.isCoinducing
  exact ⟨(continuous_const_vadd c).comp hf.continuous, fun x => map_vadd f c x⟩

end Additive

end GroupTheoryTest.Topology.Algebra.ConstMulAction
