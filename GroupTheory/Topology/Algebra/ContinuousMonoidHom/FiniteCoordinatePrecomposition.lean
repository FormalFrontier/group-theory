/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateSupport

/-!
# Coordinate supports under coordinatewise precomposition

Coordinate restrictions commute with precomposition by a family of multiplicative
unital maps. Precomposition can only decrease the coordinate support, and it preserves
the support at every coordinate where the corresponding map is surjective.

The factor families and the target need only be unital magmas; no associativity,
commutativity, inversion or topological hypotheses are required.
-/

@[expose] public section

universe u v w z

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {H : ι → Type w} {D : Type z}
  [∀ i, MulOneClass (G i)] [∀ i, MulOneClass (H i)] [MulOneClass D]

/-- Restricting a coordinatewise pullback is the pullback of the coordinate restriction. -/
theorem coordinateHom_comp_piMap (f : (∀ i, H i) →* D) (q : ∀ i, G i →* H i) (i : ι) :
    (f.comp (MonoidHom.piMap q)).coordinateHom i = (f.coordinateHom i).comp (q i) := by
  classical
  ext a
  have hs : MonoidHom.piMap q (Pi.mulSingle i a) = Pi.mulSingle i (q i a) := by
    funext j
    exact Pi.apply_mulSingle (fun j x => q j x) (fun j => (q j).map_one) i a j
  calc
    (f.comp (MonoidHom.piMap q)).coordinateHom i a =
        (f.comp (MonoidHom.piMap q)) (Pi.mulSingle i a) := coordinateHom_apply _ _ _
    _ = f (Pi.mulSingle i (q i a)) := congrArg f hs
    _ = (f.coordinateHom i).comp (q i) a := (coordinateHom_apply f i (q i a)).symm

/-- Coordinatewise precomposition cannot create a nontrivial coordinate restriction. -/
theorem coordinateMulSupport_comp_piMap_subset (f : (∀ i, H i) →* D)
    (q : ∀ i, G i →* H i) :
    (f.comp (MonoidHom.piMap q)).coordinateMulSupport ⊆ f.coordinateMulSupport := by
  intro i hi
  rcases (mem_coordinateMulSupport_iff (f.comp (MonoidHom.piMap q)) i).mp hi with ⟨a, ha⟩
  rw [coordinateHom_comp_piMap] at ha
  exact (mem_coordinateMulSupport_iff f i).mpr ⟨q i a, ha⟩

/-- Surjectivity at one coordinate preserves detection of that coordinate. -/
theorem mem_coordinateMulSupport_comp_piMap_iff_of_surjective (f : (∀ i, H i) →* D)
    (q : ∀ i, G i →* H i) (i : ι) (hq : Function.Surjective (q i)) :
    i ∈ (f.comp (MonoidHom.piMap q)).coordinateMulSupport ↔ i ∈ f.coordinateMulSupport := by
  constructor
  · exact fun hi => coordinateMulSupport_comp_piMap_subset f q hi
  · intro hi
    rcases (mem_coordinateMulSupport_iff f i).mp hi with ⟨b, hb⟩
    rcases hq b with ⟨a, rfl⟩
    apply (mem_coordinateMulSupport_iff (f.comp (MonoidHom.piMap q)) i).mpr
    refine ⟨a, ?_⟩
    rw [coordinateHom_comp_piMap]
    exact hb

/-- Coordinatewise surjective precomposition preserves the coordinate support. -/
theorem coordinateMulSupport_comp_piMap_of_surjective (f : (∀ i, H i) →* D)
    (q : ∀ i, G i →* H i) (hq : ∀ i, Function.Surjective (q i)) :
    (f.comp (MonoidHom.piMap q)).coordinateMulSupport = f.coordinateMulSupport := by
  ext i
  exact mem_coordinateMulSupport_comp_piMap_iff_of_surjective f q i (hq i)

end MonoidHom
