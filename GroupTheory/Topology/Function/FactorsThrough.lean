/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed fibreconstancy constraints

A family of functions with continuous point evaluations satisfies a closed fibreconstancy
constraint when its target is Hausdorff. The indexing sorts need no topology or algebraic
structure, and the map defining the fibres need not be continuous or surjective.

## References

The logical predicate is Mathlib's `Function.FactorsThrough`, from
`Mathlib.Logic.Function.Basic`. The equalizer argument uses the Mathlib community's
`isClosed_eq` API in `Mathlib.Topology.Separation.Hausdorff` and arbitrary intersections of
closed sets.
-/

@[expose] public section

universe u v w z

namespace Function

/-- Fibreconstancy defines a closed constraint on a family with continuous point evaluations
and Hausdorff target. No structure or topology on the indexing sorts is required. -/
theorem isClosed_setOf_factorsThrough {A : Sort u} {S : Sort v}
    {P : Type w} {K : Type z} [TopologicalSpace P] [TopologicalSpace K] [T2Space K]
    (q : A → S) (e : P → A → K) (he : ∀ a, Continuous (fun p : P ↦ e p a)) :
    IsClosed {p : P | FactorsThrough (e p) q} := by
  simp only [FactorsThrough, Set.ofPred_forall]
  exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
    isClosed_iInter fun _ ↦ isClosed_eq (he a) (he b)

end Function
