/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Sections
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Separation.Basic

/-!
# Boundary cases for continuous compatible sections

The sections construction includes empty indexing categories, non-group monoids,
indiscrete stages, and diagrams with two distinct parallel arrows, including
arrows that are not continuous for the chosen stage topologies.
-/

public section

namespace GroupTheoryTest.Topology.Sections

/-- The additive group of `ZMod 2`, written multiplicatively, is nontrivial. -/
theorem twoGroup_nontrivial : Nontrivial (Multiplicative (ZMod 2)) := inferInstance

end GroupTheoryTest.Topology.Sections

end

section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace GroupTheoryTest.Topology.Sections

/-- The additive group of `ZMod 2` in multiplicative notation. -/
public abbrev TwoGroup := Multiplicative (ZMod 2)

private instance : TopologicalSpace TwoGroup := ⊥

private instance : DiscreteTopology TwoGroup := ⟨rfl⟩

/-- A monoid diagram with no stages. -/
public abbrev emptyDiagram : Discrete PEmpty ⥤ MonCat :=
  (Functor.const (Discrete PEmpty)).obj (MonCat.of TwoGroup)

private instance : ∀ j : Discrete PEmpty, TopologicalSpace (emptyDiagram.obj j) :=
  fun j => j.as.elim

private instance : ∀ j : Discrete PEmpty,
    TopologicalSpace ((emptyDiagram ⋙ forget MonCat).obj j) :=
  fun j => j.as.elim

private def emptyCoordinates : ∀ j : Discrete PEmpty, TwoGroup →ₜ* emptyDiagram.obj j :=
  fun j => j.as.elim

private theorem emptyCompatible :
    ∀ {i j : Discrete PEmpty} (f : i ⟶ j) (x : TwoGroup),
      emptyDiagram.map f (emptyCoordinates i x) = emptyCoordinates j x := by
  intro i
  exact i.as.elim

example : ∃! g : TwoGroup →ₜ* (emptyDiagram ⋙ forget MonCat).sections,
    ∀ j : Discrete PEmpty,
      (MonCat.sectionsπContinuousMonoidHom emptyDiagram j).comp g = emptyCoordinates j := by
  refine ⟨MonCat.sectionsLift emptyDiagram emptyCoordinates emptyCompatible, ?_, ?_⟩
  · intro j
    exact j.as.elim
  · intro g hg
    exact MonCat.sectionsLift_unique emptyDiagram emptyCoordinates emptyCompatible g hg

/-- A one-stage monoid diagram whose stage is not a group. -/
public abbrev natDiagram : Discrete PUnit ⥤ MonCat :=
  (Functor.const (Discrete PUnit)).obj (MonCat.of ℕ)

private instance : TopologicalSpace ℕ := ⊥

private instance : ∀ j : Discrete PUnit, TopologicalSpace (natDiagram.obj j) :=
  fun _ => ⊥

example (number : ℕ) :
    MonCat.sectionsπContinuousMonoidHom natDiagram (Discrete.mk PUnit.unit)
        (MonCat.sectionsLift natDiagram (fun _ => ContinuousMonoidHom.id ℕ)
          (by intro i j f x; rfl) number) = number := by
  exact MonCat.sectionsπ_sectionsLift_apply natDiagram _ _ _ number

/-- The two projections out of a product as parallel arrows. -/
public abbrev pairDiagram : WalkingParallelPair ⥤ MonCat :=
  parallelPair (MonCat.ofHom (MonoidHom.fst TwoGroup TwoGroup))
    (MonCat.ofHom (MonoidHom.snd TwoGroup TwoGroup))

private instance : ∀ j : WalkingParallelPair, TopologicalSpace (pairDiagram.obj j) :=
  fun _ => ⊥

private def diagonalCoordinates :
    ∀ j : WalkingParallelPair, TwoGroup →ₜ* pairDiagram.obj j
  | .zero =>
    { toFun := fun element => (element, element)
      map_one' := rfl
      map_mul' := by intro _ _; rfl
      continuous_toFun := continuous_of_discreteTopology }
  | .one => ContinuousMonoidHom.id TwoGroup

private theorem diagonalCompatible :
    ∀ {i j : WalkingParallelPair} (f : i ⟶ j) (x : TwoGroup),
      pairDiagram.map f (diagonalCoordinates i x) = diagonalCoordinates j x := by
  intro i j f x
  cases f <;> rfl

example (element : TwoGroup) :
    ((MonCat.sectionsHomEquiv pairDiagram).symm
      ⟨diagonalCoordinates, diagonalCompatible⟩ element).val WalkingParallelPair.zero =
        (element, element) := by
  rfl

example (element : TwoGroup) :
    ((MonCat.sectionsHomEquiv pairDiagram)
      (MonCat.sectionsLift pairDiagram diagonalCoordinates diagonalCompatible)).val
        WalkingParallelPair.zero element = (element, element) := by
  rfl

example (element : TwoGroup) :
    pairDiagram.map WalkingParallelPairHom.left
        ((MonCat.sectionsLift pairDiagram diagonalCoordinates diagonalCompatible element).val
          WalkingParallelPair.zero) = element ∧
      pairDiagram.map WalkingParallelPairHom.right
        ((MonCat.sectionsLift pairDiagram diagonalCoordinates diagonalCompatible element).val
          WalkingParallelPair.zero) = element := by
  exact ⟨rfl, rfl⟩

/-- A one-stage group diagram. -/
public abbrev groupPointDiagram : Discrete PUnit ⥤ GrpCat :=
  (Functor.const (Discrete PUnit)).obj (GrpCat.of TwoGroup)

private instance : ∀ j : Discrete PUnit, TopologicalSpace (groupPointDiagram.obj j) :=
  fun _ => ⊥

private instance : ∀ j : Discrete PUnit,
    TopologicalSpace ((groupPointDiagram ⋙ forget₂ GrpCat MonCat).obj j) :=
  fun _ => ⊥

private instance : ∀ j : Discrete PUnit,
    TopologicalSpace ((groupPointDiagram ⋙ forget GrpCat).obj j) :=
  fun _ => ⊥

example (element : TwoGroup) :
    GrpCat.sectionsπContinuousMonoidHom groupPointDiagram (Discrete.mk PUnit.unit)
        (MonCat.sectionsLift (groupPointDiagram ⋙ forget₂ GrpCat MonCat)
          (fun _ => ContinuousMonoidHom.id TwoGroup)
          (by intro i j f x; rfl) element) = element := by
  rfl

section IndiscreteStage

local instance : TopologicalSpace TwoGroup := ⊤

local instance : ∀ j : Discrete PUnit, TopologicalSpace (groupPointDiagram.obj j) :=
  fun _ => ⊤

local instance : ∀ j : Discrete PUnit,
    TopologicalSpace ((groupPointDiagram ⋙ forget₂ GrpCat MonCat).obj j) :=
  fun _ => ⊤

local instance : ∀ j : Discrete PUnit,
    TopologicalSpace ((groupPointDiagram ⋙ forget GrpCat).obj j) :=
  fun _ => ⊤

local instance : ∀ j : Discrete PUnit,
    TopologicalSpace (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).obj j) :=
  fun j => (inferInstance : TopologicalSpace
    ((groupPointDiagram ⋙ forget₂ GrpCat MonCat).obj j))

example : IndiscreteTopology
    (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).sections) := by
  refine ⟨?_⟩
  have htop :
      (inferInstance : TopologicalSpace
        (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).sections)) =
        ⨅ j : Discrete PUnit, TopologicalSpace.induced
          (fun s : (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).sections) =>
            s.val j)
          (inferInstance : TopologicalSpace
            ((groupPointDiagram ⋙ forget₂ GrpCat MonCat).obj j)) := by
    convert MonCat.sections_topology (groupPointDiagram ⋙ forget₂ GrpCat MonCat) using 1
  refine htop.trans (iInf_eq_top.mpr ?_)
  intro j
  change TopologicalSpace.induced
      (fun s : (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).sections) =>
        s.val j)
      (⊤ : TopologicalSpace ((groupPointDiagram ⋙ forget₂ GrpCat MonCat).obj j)) = ⊤
  exact induced_top

example : Nontrivial
    (((groupPointDiagram ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat).sections) := by
  obtain ⟨first, second, hne⟩ := twoGroup_nontrivial.exists_pair_ne
  let lift := MonCat.sectionsLift (groupPointDiagram ⋙ forget₂ GrpCat MonCat)
    (fun _ => ContinuousMonoidHom.id TwoGroup) (by intro i j f x; rfl)
  refine ⟨⟨lift first, lift second, ?_⟩⟩
  intro heq
  apply hne
  have h := congrArg
    (MonCat.sectionsπContinuousMonoidHom (groupPointDiagram ⋙ forget₂ GrpCat MonCat)
      (Discrete.mk PUnit.unit)) heq
  change first = second at h
  exact h

example (element : TwoGroup) :
    GrpCat.sectionsπContinuousMonoidHom groupPointDiagram (Discrete.mk PUnit.unit)
        (MonCat.sectionsLift (groupPointDiagram ⋙ forget₂ GrpCat MonCat)
          (fun _ => ContinuousMonoidHom.id TwoGroup)
          (by intro i j f x; rfl) element) = element := by
  have : IndiscreteTopology TwoGroup := ⟨rfl⟩
  rfl

end IndiscreteStage

/-- Two copies of the homomorphism from the terminal group to a two-element group. -/
public abbrev terminalDiagram : WalkingParallelPair ⥤ GrpCat :=
  parallelPair (GrpCat.ofHom (1 : PUnit →* TwoGroup))
    (GrpCat.ofHom (1 : PUnit →* TwoGroup))

private theorem terminalCoordinate_one
    (compatibleSection : (terminalDiagram ⋙ forget GrpCat).sections) :
    compatibleSection.val WalkingParallelPair.one = 1 := by
  have compatibility := compatibleSection.property WalkingParallelPairHom.left
  simpa [terminalDiagram] using compatibility.symm

private instance : ∀ j : WalkingParallelPair, TopologicalSpace (terminalDiagram.obj j) :=
  fun _ => ⊥

example : ¬ Function.Surjective
    (GrpCat.sectionsπContinuousMonoidHom terminalDiagram WalkingParallelPair.one) := by
  intro surjective
  obtain ⟨element, hne⟩ := exists_ne (1 : TwoGroup)
  obtain ⟨compatibleSection, heq⟩ := surjective element
  exact hne (heq.symm.trans (terminalCoordinate_one compatibleSection))

/-- Two parallel identity homomorphisms with different stage topologies. -/
public abbrev discontinuousDiagram : WalkingParallelPair ⥤ MonCat :=
  parallelPair (MonCat.ofHom (MonoidHom.id TwoGroup))
    (MonCat.ofHom (MonoidHom.id TwoGroup))

private instance : ∀ j : WalkingParallelPair, TopologicalSpace (discontinuousDiagram.obj j) :=
  fun j => match j with
    | .zero => ⊤
    | .one => ⊥

example : ¬ Continuous[⊤, ⊥]
    (discontinuousDiagram.map WalkingParallelPairHom.left : TwoGroup → TwoGroup) := by
  change ¬ Continuous[⊤, ⊥] (id : TwoGroup → TwoGroup)
  intro continuous
  have hle : (⊤ : TopologicalSpace TwoGroup) ≤ ⊥ := continuous_id_iff_le.mp continuous
  have hIndiscrete : IndiscreteTopology TwoGroup := ⟨le_antisymm bot_le hle⟩
  exact (not_subsingleton TwoGroup) (subsingleton_iff_indiscreteTopology.mpr hIndiscrete)

private def discontinuousCoordinates :
    ∀ j : WalkingParallelPair, TwoGroup →ₜ* discontinuousDiagram.obj j
  | .zero =>
    { toMonoidHom := MonoidHom.id TwoGroup
      continuous_toFun := continuous_of_discreteTopology }
  | .one => ContinuousMonoidHom.id TwoGroup

private theorem discontinuousCompatible :
    ∀ {i j : WalkingParallelPair} (f : i ⟶ j) (x : TwoGroup),
      discontinuousDiagram.map f (discontinuousCoordinates i x) =
        discontinuousCoordinates j x := by
  intro i j f x
  cases f <;> rfl

example (element : TwoGroup) :
    (MonCat.sectionsLift discontinuousDiagram discontinuousCoordinates
      discontinuousCompatible element).val WalkingParallelPair.one = element := by
  rfl

end GroupTheoryTest.Topology.Sections

end
