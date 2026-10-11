/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Compact-open spaces of maps to discrete targets

If the domain is compact and the codomain is discrete, the compact-open topology on
continuous maps is discrete. Neither Hausdorffness nor nonemptiness is required.

The proof uses the finite range of a continuous map, compact closed fibers and
compact-open subbasic sets.

## References

- Formal Frontier Agents, *Continuous Group Cohomology*, compact/discrete
  continuous-map formalization.
- Mathlib, `Mathlib.Topology.CompactOpen` (compact-open subbasic sets) and
  its compactness and discrete-space APIs.
-/

public section

namespace ContinuousMap

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [DiscreteTopology Y]

/-- Every continuous map from a compact space to a discrete space is isolated in the
compact-open topology. In particular, this holds for empty or non-Hausdorff domains. -/
theorem discreteTopology_of_compactSpace : DiscreteTopology C(X, Y) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro f
  have finite_range : (Set.range f).Finite :=
    (isCompact_range f.continuous).finite_of_discrete
  let fiber : Y → Set X := fun y => f ⁻¹' {y}
  have compact_fiber (y : Y) : IsCompact (fiber y) :=
    ((isClosed_discrete {y}).preimage f.continuous).isCompact
  have singleton_eq : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (fiber y) {y}} := by
    ext g
    constructor
    · intro hg
      have hgf : g = f := Set.mem_singleton_iff.mp hg
      subst g
      refine Set.mem_iInter.mpr fun y => Set.mem_iInter.mpr fun _ => ?_
      intro x hx
      exact hx
    · intro hg
      apply Set.mem_singleton_iff.mpr
      ext x
      have hmap : Set.MapsTo g (fiber (f x)) {f x} :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hg (f x)) ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mp (hmap (by simp [fiber]))
  rw [singleton_eq]
  exact finite_range.isOpen_biInter fun y _ =>
    isOpen_setOfPred_mapsTo (compact_fiber y) (isOpen_discrete _)

end ContinuousMap
