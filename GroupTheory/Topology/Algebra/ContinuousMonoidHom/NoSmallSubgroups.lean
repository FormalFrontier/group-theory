module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.CompactOpen

/-!
# Discreteness of continuous homomorphisms into groups with no small subgroups

For a compact monoid `M` and a commutative topological group `G` with no small
subgroups, the compact-open topology on `M →ₜ* G` is discrete. No compatibility
between the monoid operations and the topology on `M` is required.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

/-- Continuous homomorphisms from a compact monoid to a commutative topological
group with no small subgroups form a discrete space in the compact-open topology. -/
theorem discreteTopology_of_noSmallSubgroups
    {M : Type u} {G : Type v}
    [Monoid M] [TopologicalSpace M] [CompactSpace M]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NoSmallSubgroups G] : DiscreteTopology (M →ₜ* G) := by
  obtain ⟨V, hV, hV_one, _, hV_pow⟩ :=
    NoSmallSubgroups.exists_open_nhds_one_pow (G := G)
  have h_open : IsOpen {f : M →ₜ* G | Set.range f ⊆ V} :=
    (ContinuousMap.isOpen_setOfPred_range_subset (X := M) hV).preimage
      (isInducing_toContinuousMap M G).continuous
  have h_eq : {f : M →ₜ* G | Set.range f ⊆ V} = ({1} : Set (M →ₜ* G)) := by
    apply Set.Subset.antisymm
    · intro f hf
      apply Set.mem_singleton_iff.mpr
      ext m
      change f m = 1
      apply hV_pow
      intro n _
      simpa only [map_pow] using hf (Set.mem_range_self (m ^ n))
    · intro f hf
      rcases Set.mem_singleton_iff.mp hf with rfl
      rintro _ ⟨m, rfl⟩
      change (1 : G) ∈ V
      exact hV_one
  exact discreteTopology_of_isOpen_singleton_one (h_eq ▸ h_open)

end ContinuousMonoidHom
