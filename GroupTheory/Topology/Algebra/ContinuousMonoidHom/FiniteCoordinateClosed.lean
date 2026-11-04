/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Coordinates
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateSupport
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Finite-coordinate reconstruction with closed unit fibers

A homomorphism with closed unit fiber sends a tuple to one whenever each
single-coordinate insertion at that tuple maps to one. This uses convergence of
finite truncations in the product topology and requires no target topology.

For continuous monoid homomorphisms, closedness of the target identity singleton
therefore characterizes containment of coordinate support by the canonical
finite-coordinate factorization. For each fixed finite coordinate set, this
factorization locus is closed in the compact-open topology. No continuity of
multiplication, source separation, or local compactness is required.
-/

@[expose] public section

open Filter Topology

universe u v w

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, MulOneClass (G i)] [MulOneClass D]
    [∀ i, TopologicalSpace (G i)]

/-- A closed unit fiber contains a tuple if all its single-coordinate values
map to one. Only the original source topologies are used; the target needs no
topology, and no multiplication is required to be continuous. -/
theorem eq_one_of_coordinate_values_eq_one_of_isClosed
    (f : (∀ i, G i) →* D)
    (hclosed : IsClosed {x : ∀ i, G i | f x = 1})
    (x : ∀ i, G i) (hx : ∀ i, f.coordinateHom i (x i) = 1) : f x = 1 := by
  classical
  have htrunc (t : Finset ι) : f (coordinateTruncation t x) = 1 := by
    simpa only [coordinateTruncation_apply, MonoidHom.one_apply] using
      (map_coordinate_truncation_eq f 1 t x (fun i _ => by
        simpa only [coordinateHom_apply, MonoidHom.one_apply] using hx i))
  by_contra hfx
  have hnhds : {y : ∀ i, G i | f y = 1}ᶜ ∈ 𝓝 x :=
    hclosed.isOpen_compl.mem_nhds hfx
  -- Apply convergence directly to this neighborhood, pulling it back to atTop.
  have haway : ∀ᶠ t : Finset ι in atTop,
      coordinateTruncation t x ∈ {y : ∀ i, G i | f y = 1}ᶜ :=
    (tendsto_coordinateTruncation x) hnhds
  -- Finsets are inhabited and directed by union, including for an empty index type.
  obtain ⟨t, ht⟩ := haway.exists
  exact ht (htrunc t)

end MonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- With closed target singleton `{1}`, containment of the coordinate support in
`s` is equivalent to the original canonical finite-coordinate factorization.
All carriers, topologies, and the coordinate restriction are the original ones;
no continuity of multiplication or target separation axiom is assumed. -/
theorem coordinateMulSupport_subset_iff_eq_finiteCoordinateFactor_comp_restrict_of_isClosed_one
    (f : (∀ i, G i) →ₜ* D) (s : Finset ι) (hOne : IsClosed ({1} : Set D)) :
    f.toMonoidHom.coordinateMulSupport ⊆ (s : Set ι) ↔
      (f : (∀ i, G i) → D) =
        (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
          (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  classical
  constructor
  · intro hs
    have houtside : ∀ i, i ∉ (s : Set ι) →
        ∀ a : G i, f.toMonoidHom.coordinateHom i a = 1 :=
      (MonoidHom.coordinateMulSupport_subset_iff_coordinate_values_eq_one
        f.toMonoidHom (s : Set ι)).1 hs
    have hclosed : IsClosed {x : ∀ i, G i | f.toMonoidHom x = 1} :=
      hOne.preimage f.continuous
    refine ContinuousMonoidHom.eq_finiteCoordinateFactor_comp_restrict_of_eq_one
      f s ?_
    intro x hx
    refine MonoidHom.eq_one_of_coordinate_values_eq_one_of_isClosed
      f.toMonoidHom hclosed x ?_
    intro i
    by_cases hi : i ∈ s
    · rw [hx i hi]
      exact (f.toMonoidHom.coordinateHom i).map_one
    · exact houtside i hi (x i)
  · intro hfactor
    exact MonoidHom.coordinateMulSupport_subset_of_eq_comp_restrict
      f.toMonoidHom (s : Set ι)
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) hfactor

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
  [Monoid D] [TopologicalSpace D]

/-- The canonical finite-coordinate reconstruction locus for a fixed `s` is closed
in the original compact-open topology if the target identity singleton is closed. -/
theorem isClosed_setOf_finiteCoordinateFactor_comp_restrict
    (s : Finset ι) (hOne : IsClosed ({1} : Set D)) :
    IsClosed {f : (∀ i, G i) →ₜ* D |
      (f : (∀ i, G i) → D) =
        (f.finiteCoordinateFactor s :
          (∀ i : {i // i ∈ s}, G i) → D) ∘
          (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i)} := by
  have hClosed :
      IsClosed {f : (∀ i, G i) →ₜ* D |
        Set.MapsTo f {z : ∀ i, G i | ∀ i ∈ s, z i = 1} ({1} : Set D)} :=
    (ContinuousMap.isClosed_setOfPred_mapsTo hOne
      {z : ∀ i, G i | ∀ i ∈ s, z i = 1}).preimage
      (isInducing_toContinuousMap (∀ i, G i) D).continuous
  have hSet :
      {f : (∀ i, G i) →ₜ* D |
        Set.MapsTo f {z : ∀ i, G i | ∀ i ∈ s, z i = 1} ({1} : Set D)} =
      {f : (∀ i, G i) →ₜ* D |
        (f : (∀ i, G i) → D) =
          (f.finiteCoordinateFactor s :
            (∀ i : {i // i ∈ s}, G i) → D) ∘
            (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i)} := by
    ext f
    constructor
    · intro hf
      apply f.eq_finiteCoordinateFactor_comp_restrict_of_eq_one s
      intro z hz
      exact Set.mem_singleton_iff.mp (hf hz)
    · intro hf z hz
      have hrestrict : (fun i : {i // i ∈ s} => z i) = 1 := by
        funext i
        exact hz i i.property
      change f z ∈ ({1} : Set D)
      apply Set.mem_singleton_iff.mpr
      calc
        f z = f.finiteCoordinateFactor s (fun i : {i // i ∈ s} => z i) :=
          congrFun hf z
        _ = f.finiteCoordinateFactor s 1 :=
          congrArg (f.finiteCoordinateFactor s) hrestrict
        _ = 1 := map_one (f.finiteCoordinateFactor s)
  rw [← hSet]
  exact hClosed

end ContinuousMonoidHom
