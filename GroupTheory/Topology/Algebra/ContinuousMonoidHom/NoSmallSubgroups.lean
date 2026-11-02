module

public import GroupTheory.Topology.Algebra.ContinuousMap.NoSmallSubgroups
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.CompactOpen

/-!
# Continuous homomorphisms into groups with no small subgroups

For a compact monoid `M` and a group `G` with continuous inversion and no small
subgroups, the trivial homomorphism is isolated in the compact-open topology on
`M →ₜ* G`. If `G` is a commutative topological group, this topology is discrete.
No compatibility between the monoid operations and the topology on `M` is required.
-/

@[expose] public section

universe u v

namespace ContinuousMonoidHom

/-- The trivial continuous homomorphism from a compact monoid to a group with
continuous inversion and no small subgroups is isolated in the compact-open topology. -/
theorem isOpen_singleton_one_of_noSmallSubgroups
    {M : Type u} {G : Type v}
    [Monoid M] [TopologicalSpace M] [CompactSpace M]
    [Group G] [TopologicalSpace G] [ContinuousInv G]
    [NoSmallSubgroups G] : IsOpen ({1} : Set (M →ₜ* G)) := by
  obtain ⟨V, hV, hV_one, _, hV_pow⟩ :=
    NoSmallSubgroups.exists_open_nhds_one_pow (G := G)
  have h_open : IsOpen {f : M →ₜ* G | Set.MapsTo f Set.univ V} :=
    (ContinuousMap.isOpen_setOfPred_mapsTo (X := M) isCompact_univ hV).preimage
      (isInducing_toContinuousMap M G).continuous
  have h_eq : {f : M →ₜ* G | Set.MapsTo f Set.univ V} = ({1} : Set (M →ₜ* G)) := by
    apply Set.Subset.antisymm
    · intro f hf
      apply Set.mem_singleton_iff.mpr
      ext m
      change f m = 1
      apply hV_pow
      intro n _
      simpa only [map_pow] using hf (Set.mem_univ (m ^ n))
    · intro f hf
      rcases Set.mem_singleton_iff.mp hf with rfl
      intro m _
      change (1 : G) ∈ V
      exact hV_one
  exact h_eq ▸ h_open

/-- Continuous homomorphisms from a compact monoid to a commutative topological
group with no small subgroups form a discrete space in the compact-open topology. -/
theorem discreteTopology_of_noSmallSubgroups
    {M : Type u} {G : Type v}
    [Monoid M] [TopologicalSpace M] [CompactSpace M]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NoSmallSubgroups G] : DiscreteTopology (M →ₜ* G) := by
  exact discreteTopology_of_isOpen_singleton_one
    (isOpen_singleton_one_of_noSmallSubgroups (M := M) (G := G))

end ContinuousMonoidHom
