/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.Algebra.Group.PiDiscreteFactor
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Basic.Finite.Prod
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Homomorphisms through selected quotient products

Projection of first components from two copies of a product of cyclic groups
uses both coordinates. It admits an explicit quotient factorization whose
coordinate kernels are proper and nontrivial. The kernel criterion and
surjectivity API recover existence and uniqueness without unfolding the
selected quotient projection. The trivial normal subgroup of the additive real
group is closed but not open; its selected quotient projection is still
surjective and distinguishes explicit nonidentity tuples.

An observer on an infinite index has an infinite discrete target and finite,
nontrivial image. In contrast, evaluation on a product of discrete integer
groups is surjective onto an infinite group: its source is not compact, and
no factorization of this homomorphism can have a finite stage. The full product
of the integer groups has the product topology, not the discrete topology.
Empty indices and the trivial cyclic target give empty-coordinate boundaries.
A dependent family of cyclic product groups supplies a heterogeneous example.

## References

- Mathlib, for cyclic groups as `Multiplicative (ZMod n)`, product homomorphisms,
  evaluation homomorphisms, quotient lifts and discrete integer topology.
- Formal Frontier Agents, finite-coordinate quotient factorization and
  finite-cylinder containment for open normal subgroups.
-/

namespace GroupTheoryTest.Topology.Algebra.Group.PiDiscreteFactor

universe uI uG uH

local notation "C₁" => Multiplicative (ZMod 1)
local notation "C₂" => Multiplicative (ZMod 2)
local notation "C₃" => Multiplicative (ZMod 3)
local notation "Z" => Multiplicative ℤ
local notation "R" => Multiplicative ℝ
local notation "A" => C₂ × C₂

private def a : C₂ := Multiplicative.ofAdd (1 : ZMod 2)

/-- The kernel of first projection, with the existing subgroup kernel. -/
private def firstKernel (B : Type uG) (D : Type uH) [Group B] [Group D]
    [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] :
    OpenNormalSubgroup (B × D) where
  toSubgroup := (MonoidHom.fst B D).ker
  isOpen' := by
    change IsOpen (Prod.fst ⁻¹' ({1} : Set B))
    exact (isOpen_discrete _).preimage continuous_fst

/-- First projection descended with Mathlib's canonical quotient homomorphism. -/
private def firstQuotient (B : Type uG) (D : Type uH) [Group B] [Group D]
    [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace D] :
    ((B × D) ⧸ (firstKernel B D).toSubgroup) →ₜ* B where
  toMonoidHom := QuotientGroup.lift (firstKernel B D).toSubgroup
    (MonoidHom.fst B D) le_rfl
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    change Continuous (fun x : B × D =>
      (QuotientGroup.lift (firstKernel B D).toSubgroup (MonoidHom.fst B D) le_rfl)
        (QuotientGroup.mk x))
    exact (continuous_fst : Continuous (Prod.fst : B × D → B)).congr fun x =>
      (QuotientGroup.lift_mk' (N := (firstKernel B D).toSubgroup)
        (φ := MonoidHom.fst B D) le_rfl x).symm

/-- Observe the first components at two coordinates by continuous homomorphisms. -/
private def firstPairAt {I : Type uI} (i j : I) : (I → A) →ₜ* (C₂ × C₂) :=
  ((ContinuousMonoidHom.fst C₂ C₂).comp
    ⟨Pi.evalMonoidHom (fun _ : I => A) i, continuous_apply i⟩).prod
    ((ContinuousMonoidHom.fst C₂ C₂).comp
      ⟨Pi.evalMonoidHom (fun _ : I => A) j, continuous_apply j⟩)

private def firstPair : (Fin 2 → A) →ₜ* (C₂ × C₂) := firstPairAt 0 1

private def spike {I : Type uI} [DecidableEq I] (j : I) : I → A :=
  fun i => if i = j then (a, 1) else 1

-- These variations change exactly the indicated coordinate, not the other one.
example :
    (∀ i : Fin 2, i ≠ 0 → spike (0 : Fin 2) i = 1) ∧
      firstPair (spike (0 : Fin 2)) ≠ firstPair (1 : Fin 2 → A) := by
  constructor
  · intro i hi
    simp [spike, hi]
  · decide

example :
    (∀ i : Fin 2, i ≠ 1 → spike (1 : Fin 2) i = 1) ∧
      firstPair (spike (1 : Fin 2)) ≠ firstPair (1 : Fin 2 → A) := by
  constructor
  · intro i hi
    simp [spike, hi]
  · decide

-- Each chosen coordinate kernel is nontrivial and proper.
example :
    (1, a) ∈ firstKernel C₂ C₂ ∧ (1, a) ≠ (1 : A) ∧
      (a, 1) ∉ firstKernel C₂ C₂ := by
  change (1 : C₂) = 1 ∧ (1, a) ≠ (1 : A) ∧ a ≠ (1 : C₂)
  decide

private def allCoordinates : Finset (Fin 2) := Finset.univ

private def coordinateKernels (_ : allCoordinates) : OpenNormalSubgroup A :=
  firstKernel C₂ C₂

/-- Closed, nonopen normal subgroups of the usual additive real factors. -/
private def realCoordinateKernels (_ : allCoordinates) : Subgroup R := ⊥

-- Normality alone supplies the projection, without quotient-discreteness assumptions.
example :
    IsClosed ((⊥ : Subgroup R) : Set R) ∧ ¬ IsOpen ((⊥ : Subgroup R) : Set R) ∧
      Function.Surjective (ContinuousMonoidHom.piQuotient
        (G := fun _ : Fin 2 => R) allCoordinates realCoordinateKernels) ∧
      ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => R)
        allCoordinates realCoordinateKernels (fun _ => Multiplicative.ofAdd (1 : ℝ)) ≠
        ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => R)
          allCoordinates realCoordinateKernels (1 : Fin 2 → R) := by
  refine ⟨?_, ?_, ContinuousMonoidHom.piQuotient_surjective
    (G := fun _ : Fin 2 => R) allCoordinates realCoordinateKernels, ?_⟩
  · change IsClosed ({0} : Set ℝ)
    exact isClosed_singleton
  · change ¬ IsOpen ({0} : Set ℝ)
    exact not_isOpen_singleton (0 : ℝ)
  · intro heq
    have hcoord := congrArg
      (fun y : ∀ i : allCoordinates, R ⧸ realCoordinateKernels i =>
        y ⟨0, Finset.mem_univ 0⟩) heq
    have hmem : Multiplicative.ofAdd (1 : ℝ) ∈ (⊥ : Subgroup R) :=
      (QuotientGroup.eq_one_iff _).mp (by
        change
          (QuotientGroup.mk (Multiplicative.ofAdd (1 : ℝ)) :
            R ⧸ (⊥ : Subgroup R)) = 1 at hcoord
        exact hcoord)
    change (1 : ℝ) = 0 at hmem
    exact one_ne_zero hmem

private def firstPairStage :
    (∀ i : allCoordinates, A ⧸ (coordinateKernels i).toSubgroup) →ₜ* (C₂ × C₂) :=
  ((firstQuotient C₂ C₂).comp
    ⟨Pi.evalMonoidHom (fun i : allCoordinates => A ⧸ (coordinateKernels i).toSubgroup)
      (⟨0, Finset.mem_univ 0⟩ : allCoordinates),
        continuous_apply (⟨0, Finset.mem_univ 0⟩ : allCoordinates)⟩).prod
    ((firstQuotient C₂ C₂).comp
      ⟨Pi.evalMonoidHom (fun i : allCoordinates => A ⧸ (coordinateKernels i).toSubgroup)
        (⟨1, Finset.mem_univ 1⟩ : allCoordinates),
          continuous_apply (⟨1, Finset.mem_univ 1⟩ : allCoordinates)⟩)

private theorem firstPairStage_comp :
    firstPairStage.comp
      (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) allCoordinates
        (fun i => (coordinateKernels i).toSubgroup)) = firstPair := by
  apply ContinuousMonoidHom.ext
  intro x
  rfl

-- An explicit factorization, independently of the existence headline.
example :
    firstPairStage.comp
      (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) allCoordinates
        (fun i => (coordinateKernels i).toSubgroup)) = firstPair ∧
      (∀ i : allCoordinates, (1, a) ∈ coordinateKernels i ∧
        (a, 1) ∉ coordinateKernels i) := by
  refine ⟨firstPairStage_comp, fun _ => ?_⟩
  change (1 : C₂) = 1 ∧ a ≠ (1 : C₂)
  decide

/-- Multiply the two observed first components in the cyclic group. -/
private def firstProduct : (Fin 2 → A) →ₜ* C₂ :=
  (ContinuousMonoidHom.mul C₂).comp firstPair

private def firstProductStage :
    (∀ i : allCoordinates, A ⧸ (coordinateKernels i).toSubgroup) →ₜ* C₂ :=
  (ContinuousMonoidHom.mul C₂).comp firstPairStage

-- Both coordinates are essential, but the descended homomorphism is not injective.
example :
    firstProductStage.comp
      (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) allCoordinates
        (fun i => (coordinateKernels i).toSubgroup)) = firstProduct ∧
      firstProduct (spike (0 : Fin 2)) ≠ firstProduct (1 : Fin 2 → A) ∧
      firstProduct (spike (1 : Fin 2)) ≠ firstProduct (1 : Fin 2 → A) ∧
      ¬ Function.Injective firstProductStage := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · ext x
    rfl
  · intro hinj
    let q := ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A)
      allCoordinates (fun i => (coordinateKernels i).toSubgroup)
    have hvalues : firstProductStage (q (fun _ => (a, 1))) =
        firstProductStage (q (1 : Fin 2 → A)) := by
      decide
    have hpair : (a, a) = ((1, 1) : C₂ × C₂) :=
      congrArg firstPairStage (hinj hvalues)
    exact (by decide : (a, a) ≠ ((1, 1) : C₂ × C₂)) hpair

-- The new projection's kernel criterion is consumed on a concrete homomorphism.
example :
    ∃! g : (∀ i : allCoordinates, A ⧸ (coordinateKernels i).toSubgroup) →ₜ* (C₂ × C₂),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) allCoordinates
        (fun i => (coordinateKernels i).toSubgroup)) = firstPair := by
  let : ∀ i : allCoordinates,
      DiscreteTopology (A ⧸ (coordinateKernels i).toSubgroup) :=
    fun i => QuotientGroup.discreteTopology (coordinateKernels i).isOpen
  let q := ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A)
    allCoordinates (fun i => (coordinateKernels i).toSubgroup)
  have hopen : IsOpenMap q := fun _ _ => isOpen_discrete _
  have hq : Topology.IsQuotientMap q := hopen.isQuotientMap q.continuous
    (ContinuousMonoidHom.piQuotient_surjective (G := fun _ : Fin 2 => A)
      allCoordinates (fun i => (coordinateKernels i).toSubgroup))
  apply (ContinuousMonoidHom.piQuotient_existsUnique_factor (G := fun _ : Fin 2 => A)
    allCoordinates (fun i => (coordinateKernels i).toSubgroup) hq firstPair).2
  intro x hx
  have hcoords := (ContinuousMonoidHom.mem_ker_piQuotient (G := fun _ : Fin 2 => A)
    allCoordinates (fun i => (coordinateKernels i).toSubgroup) x).mp hx
  change ((x 0).1, (x 1).1) = (1, 1)
  exact Prod.ext (hcoords ⟨0, Finset.mem_univ 0⟩) (hcoords ⟨1, Finset.mem_univ 1⟩)

-- Uniqueness uses surjectivity and the existing bundled-hom extensionality.
example
    (g : (∀ i : allCoordinates, A ⧸ (coordinateKernels i).toSubgroup) →ₜ* (C₂ × C₂))
    (hg : g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) allCoordinates
      (fun i => (coordinateKernels i).toSubgroup)) = firstPair) : g = firstPairStage := by
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := ContinuousMonoidHom.piQuotient_surjective (G := fun _ : Fin 2 => A)
    allCoordinates (fun i => (coordinateKernels i).toSubgroup) y
  exact congrArg (fun k : (Fin 2 → A) →ₜ* (C₂ × C₂) => k x)
    (hg.trans firstPairStage_comp.symm)

/-- Every factorization of this observer must keep both essential coordinates. -/
private theorem firstPair_factor_support
    (s : Finset (Fin 2)) (N : ∀ _ : s, OpenNormalSubgroup A)
    (g : (∀ i : s, A ⧸ (N i).toSubgroup) →ₜ* (C₂ × C₂))
    (hg : g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) s
      (fun i => (N i).toSubgroup)) = firstPair) :
    (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by
  have triangle (x : Fin 2 → A) :
      g (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) s
        (fun i => (N i).toSubgroup) x) = firstPair x :=
    congrArg (fun k : (Fin 2 → A) →ₜ* (C₂ × C₂) => k x) hg
  have hne : ∀ j : Fin 2, firstPair (spike j) ≠ firstPair (1 : Fin 2 → A) := by
    decide
  have hsupport (j : Fin 2) : j ∈ s := by
    by_contra hj
    have hq : ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) s
        (fun i => (N i).toSubgroup) (spike j) =
        ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) s
          (fun i => (N i).toSubgroup) (1 : Fin 2 → A) := by
      funext i
      have hij : (i : Fin 2) ≠ j := by
        intro hij
        exact hj (hij ▸ i.property)
      simp [spike, hij]
    exact hne j ((triangle _).symm.trans ((congrArg g hq).trans (triangle _)))
  exact ⟨hsupport 0, hsupport 1⟩

-- The compact headline supplies a finite stage that must retain both coordinates.
example :
    ∃ (s : Finset (Fin 2)) (N : ∀ _ : s, OpenNormalSubgroup A)
      (g : (∀ i : s, A ⧸ (N i).toSubgroup) →ₜ* (C₂ × C₂)),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => A) s
        (fun i => (N i).toSubgroup)) = firstPair ∧
      Finite (∀ i : s, A ⧸ (N i).toSubgroup) ∧
      (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by
  obtain ⟨s, N, g, hg, _, hfinite, _⟩ :=
    ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor_finite
      (G := fun _ : Fin 2 => A) firstPair
  exact ⟨s, N, g, hg, hfinite, firstPair_factor_support s N g hg⟩

/-- Observe two discrete first components while ignoring arbitrary topological
factors whose group operations are not assumed continuous. -/
private def firstPairWithTail (T : Type uG) [Group T] [TopologicalSpace T] :
    (Fin 2 → C₂ × T) →ₜ* (C₂ × C₂) :=
  ((ContinuousMonoidHom.fst C₂ T).comp
    ⟨Pi.evalMonoidHom (fun _ : Fin 2 => C₂ × T) 0, continuous_apply 0⟩).prod
    ((ContinuousMonoidHom.fst C₂ T).comp
      ⟨Pi.evalMonoidHom (fun _ : Fin 2 => C₂ × T) 1, continuous_apply 1⟩)

-- No multiplication-continuity instance is available for the ignored factor.
example {T : Type uG} [Group T] [TopologicalSpace T] :
    ∃ (s : Finset (Fin 2)) (N : ∀ _ : s, OpenNormalSubgroup (C₂ × T))
      (g : (∀ i : s, (C₂ × T) ⧸ (N i).toSubgroup) →ₜ* (C₂ × C₂)),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Fin 2 => C₂ × T) s
        (fun i => (N i).toSubgroup)) = firstPairWithTail T ∧
      (∀ i : s, DiscreteTopology ((C₂ × T) ⧸ (N i).toSubgroup)) ∧
      firstPairWithTail T (fun i => if i = 0 then (a, 1) else 1) ≠ 1 := by
  obtain ⟨s, N, g, hg, hdiscrete, _⟩ :=
    ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor
      (G := fun _ : Fin 2 => C₂ × T) (firstPairWithTail T)
  refine ⟨s, N, g, hg, hdiscrete, ?_⟩
  intro heq
  have ha : a = (1 : C₂) := congrArg Prod.fst heq
  exact (by decide : a ≠ (1 : C₂)) ha

/-- An infinite target is allowed; only the first two finite components vary. -/
private def labelledFirstPair : (ℕ → A) →ₜ* ((C₂ × C₂) × Z) :=
  (firstPairAt (0 : ℕ) 1).prod 1

example : Infinite ((C₂ × C₂) × Z) := inferInstance

example :
    (Set.range labelledFirstPair).Finite ∧
      labelledFirstPair (spike (0 : ℕ)) ≠ labelledFirstPair (1 : ℕ → A) := by
  constructor
  · have hfinite : (Set.range (fun p : C₂ × C₂ => (p, (1 : Z)))).Finite :=
      Set.finite_range _
    apply hfinite.subset
    rintro _ ⟨x, rfl⟩
    exact ⟨firstPairAt (0 : ℕ) 1 x, rfl⟩
  · decide

-- The selected quotient product is finite, although the index and target are infinite.
example :
    ∃ (s : Finset ℕ) (N : ∀ _ : s, OpenNormalSubgroup A)
      (g : (∀ i : s, A ⧸ (N i).toSubgroup) →ₜ* ((C₂ × C₂) × Z)),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => A) s
        (fun i => (N i).toSubgroup)) = labelledFirstPair ∧
      Finite (∀ i : s, A ⧸ (N i).toSubgroup) ∧
      DiscreteTopology (∀ i : s, A ⧸ (N i).toSubgroup) ∧
      g (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => A) s
        (fun i => (N i).toSubgroup) (spike (0 : ℕ))) ≠
        g (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => A) s
          (fun i => (N i).toSubgroup) (1 : ℕ → A)) := by
  obtain ⟨s, N, g, hg, _, hfinite, hdiscrete⟩ :=
    ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor_finite
      (G := fun _ : ℕ => A) labelledFirstPair
  refine ⟨s, N, g, hg, hfinite, hdiscrete, ?_⟩
  have triangle (x : ℕ → A) :
      g (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => A) s
        (fun i => (N i).toSubgroup) x) = labelledFirstPair x :=
    congrArg (fun k : (ℕ → A) →ₜ* ((C₂ × C₂) × Z) => k x) hg
  rw [triangle, triangle]
  decide

/-- Surjective integer evaluation has open kernel but infinite image. -/
private def integerEval : (ℕ → Z) →ₜ* Z :=
  ⟨Pi.evalMonoidHom (fun _ : ℕ => Z) 0, continuous_apply 0⟩

private theorem integerEval_surjective : Function.Surjective integerEval := by
  intro z
  exact ⟨fun _ => z, rfl⟩

example : DiscreteTopology Z ∧ Infinite Z := ⟨inferInstance, inferInstance⟩

example : ¬ CompactSpace (ℕ → Z) := by
  intro hcompact
  let : CompactSpace (ℕ → Z) := hcompact
  let : CompactSpace Z := integerEval_surjective.compactSpace integerEval.continuous
  exact (finite_of_compact_of_discrete (X := Z)).false

/-- A surjective infinite-image observer cannot factor through a finite stage. -/
private theorem integerEval_stage_not_finite
    (s : Finset ℕ) (N : ∀ _ : s, OpenNormalSubgroup Z)
    (g : (∀ i : s, Z ⧸ (N i).toSubgroup) →ₜ* Z)
    (hg : g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => Z) s
      (fun i => (N i).toSubgroup)) = integerEval) :
    ¬ Finite (∀ i : s, Z ⧸ (N i).toSubgroup) := by
  intro hfinite
  let : Finite (∀ i : s, Z ⧸ (N i).toSubgroup) := hfinite
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨x, hx⟩ := integerEval_surjective z
    refine ⟨ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => Z) s
      (fun i => (N i).toSubgroup) x, ?_⟩
    exact (congrArg (fun k : (ℕ → Z) →ₜ* Z => k x) hg).trans hx
  have htarget : Finite Z := Set.finite_univ_iff.mp (by
    simpa only [hsurj.range_eq] using (Set.finite_range g))
  exact htarget.false

-- The generic headline must not promise finite quotients or finite image.
example :
    ∃ (s : Finset ℕ) (N : ∀ _ : s, OpenNormalSubgroup Z)
      (g : (∀ i : s, Z ⧸ (N i).toSubgroup) →ₜ* Z),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : ℕ => Z) s
        (fun i => (N i).toSubgroup)) = integerEval ∧
      ¬ Finite (∀ i : s, Z ⧸ (N i).toSubgroup) := by
  obtain ⟨s, N, g, hg, _, _⟩ :=
    ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor (G := fun _ : ℕ => Z) integerEval
  exact ⟨s, N, g, hg, integerEval_stage_not_finite s N g hg⟩

-- The empty-index product is a trivial group, not an empty source type.
example {H : Type uH} [Group H] [TopologicalSpace H]
    (f : (Empty → Z) →ₜ* H) :
    ∃ (N : ∀ _ : (∅ : Finset Empty), OpenNormalSubgroup Z)
      (g : (∀ i : (∅ : Finset Empty), Z ⧸ (N i).toSubgroup) →ₜ* H),
      g.comp (ContinuousMonoidHom.piQuotient (G := fun _ : Empty => Z) ∅
        (fun i => (N i).toSubgroup)) = f := by
  let N : ∀ i : (∅ : Finset Empty), OpenNormalSubgroup Z := fun i => Empty.elim i.val
  refine ⟨N, 1, ?_⟩
  ext x
  have hx : x = (1 : Empty → Z) := by
    funext i
    exact Empty.elim i
  change (1 : H) = f x
  rw [hx, map_one]

-- A homomorphism into the trivial cyclic group has an empty-coordinate stage.
example {I : Type uI} {G : I → Type uG} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] (f : (∀ i, G i) →ₜ* C₁) :
    ∃ (N : ∀ i : (∅ : Finset I), OpenNormalSubgroup (G i))
      (g : (∀ i : (∅ : Finset I), G i ⧸ (N i).toSubgroup) →ₜ* C₁),
      g.comp (ContinuousMonoidHom.piQuotient (G := G) ∅ (fun i => (N i).toSubgroup)) = f := by
  let N : ∀ i : (∅ : Finset I), OpenNormalSubgroup (G i) :=
    fun i : (∅ : Finset I) =>
      False.elim (Finset.notMem_empty (i : I) (Finset.mem_coe.mp i.property))
  refine ⟨N, 1, ?_⟩
  exact ContinuousMonoidHom.ext fun _ => Subsingleton.elim _ _

/-- The factors genuinely depend on the coordinate. -/
private def cyclicFactors : Bool → Type
  | false => C₂ × C₂
  | true => C₃ × C₂

private instance (i : Bool) : Group (cyclicFactors i) := by
  cases i <;> dsimp [cyclicFactors] <;> infer_instance

private instance (i : Bool) : TopologicalSpace (cyclicFactors i) := by
  cases i <;> dsimp [cyclicFactors] <;> infer_instance

private instance (i : Bool) : DiscreteTopology (cyclicFactors i) := by
  cases i <;> dsimp [cyclicFactors] <;> infer_instance

private instance (i : Bool) : Finite (cyclicFactors i) := by
  cases i <;> dsimp [cyclicFactors] <;> infer_instance

/-- Project first components from two different cyclic product groups. -/
private def heterogeneousFirstPair : (∀ i, cyclicFactors i) →ₜ* (C₂ × C₃) :=
  ((ContinuousMonoidHom.fst C₂ C₂).comp
    ⟨Pi.evalMonoidHom cyclicFactors false, continuous_apply false⟩).prod
    ((ContinuousMonoidHom.fst C₃ C₂).comp
      ⟨Pi.evalMonoidHom cyclicFactors true, continuous_apply true⟩)

private def cyclicValues (b : C₂) (c : C₃) : ∀ i, cyclicFactors i
  | false => (b, 1)
  | true => (c, 1)

example :
    heterogeneousFirstPair (cyclicValues a 1) ≠ heterogeneousFirstPair (cyclicValues 1 1) ∧
      heterogeneousFirstPair (cyclicValues 1 (Multiplicative.ofAdd (1 : ZMod 3))) ≠
        heterogeneousFirstPair (cyclicValues 1 1) := by
  decide

example :
    ∃ (s : Finset Bool) (N : ∀ i : s, OpenNormalSubgroup (cyclicFactors i))
      (g : (∀ i : s, cyclicFactors i ⧸ (N i).toSubgroup) →ₜ* (C₂ × C₃)),
      g.comp (ContinuousMonoidHom.piQuotient (G := cyclicFactors) s (fun i => (N i).toSubgroup)) =
        heterogeneousFirstPair ∧
      (∀ i : s, Finite (cyclicFactors i ⧸ (N i).toSubgroup)) ∧
      Finite (∀ i : s, cyclicFactors i ⧸ (N i).toSubgroup) ∧
      DiscreteTopology (∀ i : s, cyclicFactors i ⧸ (N i).toSubgroup) := by
  exact ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor_finite (G := cyclicFactors)
    heterogeneousFirstPair

end GroupTheoryTest.Topology.Algebra.Group.PiDiscreteFactor
