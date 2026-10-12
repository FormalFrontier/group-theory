/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Topology.Algebra.CompactGroup.PiDiscreteFactor
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Basic.Finite.Prod
import Mathlib.Topology.Instances.ZMod

/-!
# Discrete observers on powers of compact groups

The Boolean observer `bothIdentity` on two copies of the cyclic group of order
two is true precisely when both coordinates are the identity. It is nonconstant,
uses both coordinates, and requires no algebraic structure on its target. For
any group structure supplied on `Bool`, it cannot be a group homomorphism.
This differs from the equality comparison of two coordinates, which admits a
homomorphism interpretation with an XNOR group law on `Bool`.

A conditional consumer considers an arbitrary finite set of coordinates and an
open normal subgroup of the base group. If a continuous map on those quotient
coordinates satisfies the factorization equation for `bothIdentity`, the subgroup
excludes the nonidentity element and the coordinate set contains both indices.
The finite-coordinate factorization theorem supplies a quotient-stage map for
this observer, and the consumer gives these separation and support constraints.
Applying the unary factorization theorem to a power instead gives a subgroup of
the power, not a subgroup of its base group.

Further examples observe only the discrete components of a product, factor an
observer with an infinite index and an infinite discrete target, and treat
empty indices and empty targets. A constant observer factors through the empty
set of coordinates. The selected quotient stage is finite and discrete without
requiring the original index type to be finite. The kernel of the second
projection is open and proper, whereas the trivial subgroup of an infinite
compact group cannot be open.

## References

- Formal Frontier Agents, the Group Theory compact/discrete factorization
  formalization and its Boolean separation examples, following the Continuous
  Group Cohomology formalization.
- Mathlib contributors: David Loeffler, topology on `ZMod`; Johan Commelin,
  Nailin Guan, Yi Song, and Xuchun Li, open subgroups and finite quotients;
  Simon Hudon, Patrick Massot, and Yury Kudryashov, product groups; Kexing Ying,
  kernels of group homomorphisms; Kyle Miller, finiteness of products; Mario
  Carneiro, finite subtypes. The product topology, continuous evaluation,
  and compact discrete space APIs are also from Mathlib.
-/

namespace GroupTheoryTest.Topology.Algebra.CompactGroup.PiDiscreteFactor

universe u v

local notation "C₂" => Multiplicative (ZMod 2)

/-- The nonidentity element of the cyclic group of order two. -/
private def a : C₂ := Multiplicative.ofAdd (1 : ZMod 2)

/-- An input with the prescribed first and second coordinate values. -/
private def twoValues (b c : C₂) : Fin 2 → C₂ :=
  fun i => if i = 0 then b else c

/-- Change only one coordinate from the identity to the nonidentity element. -/
private def spike {I : Type u} [DecidableEq I] (j : I) : I → C₂ :=
  fun i => if i = j then a else 1

/-- Observe identity at two coordinates, using only continuous evaluations. -/
private def bothIdentityAt {I : Type u} (i j : I) : C((I → C₂), Bool) :=
  ⟨fun x => decide (x i = 1 ∧ x j = 1),
    (show Continuous (fun p : C₂ × C₂ => decide (p.1 = 1 ∧ p.2 = 1))
      from continuous_of_discreteTopology).comp
        (f := fun x : I → C₂ => (x i, x j))
        ((continuous_apply i).prodMk (continuous_apply j))⟩

/-- The two-coordinate Boolean observer, with no target group structure. -/
private def bothIdentity : C((Fin 2 → C₂), Bool) := bothIdentityAt 0 1

example :
    bothIdentity (twoValues 1 1) = true ∧
    bothIdentity (twoValues a 1) = false ∧
    bothIdentity (twoValues 1 a) = false ∧
    bothIdentity (twoValues a a) = false := by
  decide

private theorem bothIdentity_one : bothIdentity (1 : Fin 2 → C₂) = true := by
  decide

private theorem bothIdentity_spike (j : Fin 2) : bothIdentity (spike j) = false := by
  exact (by decide : ∀ k : Fin 2, bothIdentity (spike k) = false) j

example : ∃ x y : Fin 2 → C₂, bothIdentity x ≠ bothIdentity y := by
  exact ⟨twoValues 1 1, twoValues a 1, by decide⟩

-- Each variation changes just the indicated coordinate.
example :
    (∀ i : Fin 2, i ≠ 0 → spike (0 : Fin 2) i = 1) ∧
      bothIdentity (spike (0 : Fin 2)) ≠ bothIdentity (1 : Fin 2 → C₂) := by
  constructor
  · intro i hi
    simp [spike, hi]
  · decide

example :
    (∀ i : Fin 2, i ≠ 1 → spike (1 : Fin 2) i = 1) ∧
      bothIdentity (spike (1 : Fin 2)) ≠ bothIdentity (1 : Fin 2 → C₂) := by
  constructor
  · intro i hi
    simp [spike, hi]
  · decide

-- The group structure on Bool is a parameter, not an installed instance.
example [Group Bool] (f : (Fin 2 → C₂) →* Bool) :
    ¬ ∀ x : Fin 2 → C₂, f x = bothIdentity x := by
  intro hf
  have hu : f (twoValues a 1) = false := (hf _).trans (by decide)
  have hv : f (twoValues 1 a) = false := (hf _).trans (by decide)
  have huv : f (twoValues a 1 * twoValues 1 a) = false :=
    (hf _).trans (by decide)
  have hmul : (false : Bool) * false = false := by
    calc
      false * false = f (twoValues a 1) * f (twoValues 1 a) := by rw [hu, hv]
      _ = f (twoValues a 1 * twoValues 1 a) := (f.map_mul _ _).symm
      _ = false := huv
  have hfalse : (false : Bool) = 1 :=
    mul_left_cancel (hmul.trans (mul_one (false : Bool)).symm)
  have htrue : (true : Bool) = 1 := by
    calc
      true = bothIdentity (1 : Fin 2 → C₂) := bothIdentity_one.symm
      _ = f 1 := (hf 1).symm
      _ = 1 := f.map_one
  exact (by decide : (true : Bool) ≠ false) (htrue.trans hfalse.symm)

/-- Consume a supplied finite-coordinate factorization, without asserting its
existence: it must separate the nonidentity element and retain both coordinates. -/
private theorem bothIdentity_factor_constraints
    (s : Finset (Fin 2)) (N : OpenNormalSubgroup C₂)
    (fbar : C((s → C₂ ⧸ N.toSubgroup), Bool))
    (hfactor : ∀ x : Fin 2 → C₂,
      fbar (fun i : s => QuotientGroup.mk (x i)) = bothIdentity x) :
    a ∉ N ∧ (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by
  have hne : ∀ j : Fin 2, bothIdentity (spike j) ≠ bothIdentity (1 : Fin 2 → C₂) := by
    intro j
    rw [bothIdentity_spike, bothIdentity_one]
    decide
  have hexcludes : a ∉ N := by
    intro hmem
    have hquot : (QuotientGroup.mk a : C₂ ⧸ N.toSubgroup) = QuotientGroup.mk 1 := by
      simpa only [QuotientGroup.mk_one] using (QuotientGroup.eq_one_iff a).mpr hmem
    have hpowers :
        (fun i : s => (QuotientGroup.mk (spike (0 : Fin 2) i) : C₂ ⧸ N.toSubgroup)) =
          (fun _ : s => (QuotientGroup.mk (1 : C₂) : C₂ ⧸ N.toSubgroup)) := by
      funext i
      by_cases hi : (i : Fin 2) = 0 <;> simp [spike, hi, hquot]
    exact hne 0 ((hfactor (spike (0 : Fin 2))).symm.trans
      ((congrArg fbar hpowers).trans (hfactor (1 : Fin 2 → C₂))))
  have hsupport : ∀ j : Fin 2, j ∈ s := by
    intro j
    by_contra hj
    have hpowers :
        (fun i : s => (QuotientGroup.mk (spike j i) : C₂ ⧸ N.toSubgroup)) =
          (fun _ : s => (QuotientGroup.mk (1 : C₂) : C₂ ⧸ N.toSubgroup)) := by
      funext i
      have hij : (i : Fin 2) ≠ j := by
        intro hij
        exact hj (hij ▸ i.property)
      simp [spike, hij]
    exact hne j ((hfactor (spike j)).symm.trans
      ((congrArg fbar hpowers).trans (hfactor (1 : Fin 2 → C₂))))
  exact ⟨hexcludes, hsupport 0, hsupport 1⟩

-- Finiteness of the base quotient is Mathlib's existing open-subgroup result.
example (s : Finset (Fin 2)) (N : OpenNormalSubgroup C₂)
    (fbar : C((s → C₂ ⧸ N.toSubgroup), Bool))
    (hfactor : ∀ x : Fin 2 → C₂,
      fbar (fun i : s => QuotientGroup.mk (x i)) = bothIdentity x) :
    Finite (C₂ ⧸ N.toSubgroup) ∧ a ∉ N ∧ (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s :=
  ⟨Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen,
    bothIdentity_factor_constraints s N fbar hfactor⟩

-- Only the selected coordinates are used in these finite-product instances.
example {I : Type u} {G : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (s : Finset I) (N : OpenNormalSubgroup G) :
    Finite (s → G ⧸ N.toSubgroup) ∧ DiscreteTopology (s → G ⧸ N.toSubgroup) := by
  let : Finite s := inferInstance
  let : Finite (G ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
  let : DiscreteTopology (G ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
  exact ⟨inferInstance, inferInstance⟩

-- Instantiate the factorization theorem and use its triangle to obtain both
-- a proper base-group quotient and both essential coordinates.
example :
    ∃ (s : Finset (Fin 2)) (N : OpenNormalSubgroup C₂)
      (fbar : C((s → C₂ ⧸ N.toSubgroup), Bool)),
      (∀ x : Fin 2 → C₂,
        fbar (fun i : s => QuotientGroup.mk (x i)) = bothIdentity x) ∧
      a ∉ N ∧ (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s := by
  obtain ⟨s, N, fbar, hfactor⟩ :=
    ContinuousMap.exists_finset_openNormalSubgroup_pi_factor bothIdentity
  exact ⟨s, N, fbar, hfactor, bothIdentity_factor_constraints s N fbar hfactor⟩

/-- The same observer ignores the first components of a product. -/
private def bothSecondIdentity {T : Type u} [TopologicalSpace T] :
    C((Fin 2 → T × C₂), Bool) :=
  ⟨fun x => bothIdentity (fun i => (x i).2),
    bothIdentity.continuous.comp
      (continuous_pi (fun i => continuous_snd.comp (continuous_apply i)))⟩

example {T : Type u} [TopologicalSpace T] (b c : Fin 2 → T) (x : Fin 2 → C₂) :
    bothSecondIdentity (fun i => (b i, x i)) =
      bothSecondIdentity (fun i => (c i, x i)) := by
  rfl

example {T : Type u} [TopologicalSpace T] (t : T) :
    bothSecondIdentity (fun i => (t, twoValues 1 1 i)) = true ∧
      bothSecondIdentity (fun i => (t, twoValues a 1 i)) = false := by
  change bothIdentity (twoValues 1 1) = true ∧ bothIdentity (twoValues a 1) = false
  decide

/-- The open normal projection kernel is `T × {1}`; no topology assumption on
`T` beyond a topological space is needed for this construction. -/
private def secondKernel {T : Type u} [Group T] [TopologicalSpace T] :
    OpenNormalSubgroup (T × C₂) where
  toSubgroup := (MonoidHom.snd T C₂).ker
  isOpen' := by
    change IsOpen (Prod.snd ⁻¹' ({1} : Set C₂))
    exact (isOpen_discrete _).preimage continuous_snd

example {T : Type u} [Group T] [TopologicalSpace T] (t : T) :
    (t, (1 : C₂)) ∈ secondKernel ∧ (t, a) ∉ secondKernel := by
  change (1 : C₂) = 1 ∧ a ≠ (1 : C₂)
  constructor
  · rfl
  · decide

-- Multiplying each input coordinate by an element of the projection kernel
-- leaves the observer unchanged.
example {T : Type u} [Group T] [TopologicalSpace T]
    (x n : Fin 2 → T × C₂) (hn : ∀ i : Fin 2, n i ∈ secondKernel) :
    bothSecondIdentity (x * n) = bothSecondIdentity x := by
  have hseconds : (fun i : Fin 2 => ((x * n) i).2) = (fun i : Fin 2 => (x i).2) := by
    funext i
    have hi : (n i).2 = 1 := hn i
    change (x i).2 * (n i).2 = (x i).2
    rw [hi, mul_one]
  exact congrArg bothIdentity hseconds

-- In particular, a compact product with an infinite first factor cannot use
-- the trivial subgroup as an open-subgroup shortcut.
example {T : Type u} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [CompactSpace T] [Infinite T] :
    ¬ IsOpen ((⊥ : Subgroup (T × C₂)) : Set (T × C₂)) := by
  intro h
  have hopen : IsOpen ({1} : Set (T × C₂)) := by
    simpa only [Subgroup.coe_bot] using h
  let : DiscreteTopology (T × C₂) := discreteTopology_of_isOpen_singleton_one hopen
  exact (finite_of_compact_of_discrete (X := T × C₂)).false

-- An infinite index still admits a nonconstant observer of just two coordinates.
example :
    bothIdentityAt (0 : ℕ) 1 (1 : ℕ → C₂) = true ∧
      bothIdentityAt (0 : ℕ) 1 (spike (0 : ℕ)) = false := by
  decide

/-- Label the Boolean observer in an infinite discrete target. Its range,
not its target, is finite. -/
private def identityLabel {I : Type u} (i j : I) : C((I → C₂), ℕ) :=
  ⟨fun x => if bothIdentityAt i j x = true then 1 else 0,
    (show Continuous (fun b : Bool => if b = true then (1 : ℕ) else 0)
      from continuous_of_discreteTopology).comp (bothIdentityAt i j).continuous⟩

example :
    identityLabel (0 : ℕ) 1 (1 : ℕ → C₂) = 1 ∧
      identityLabel (0 : ℕ) 1 (spike (0 : ℕ)) = 0 := by
  decide

-- The infinite-index label descends to a finite discrete selected stage, on
-- which the identity input and the spike still have different labels.
example :
    ∃ (s : Finset ℕ) (N : OpenNormalSubgroup C₂)
      (fbar : C((s → C₂ ⧸ N.toSubgroup), ℕ)),
      (∀ x : ℕ → C₂,
        fbar (fun i : s => QuotientGroup.mk (x i)) = identityLabel (0 : ℕ) 1 x) ∧
      Finite (s → C₂ ⧸ N.toSubgroup) ∧ DiscreteTopology (s → C₂ ⧸ N.toSubgroup) ∧
      fbar (fun _ : s => QuotientGroup.mk (1 : C₂)) = 1 ∧
      fbar (fun i : s => QuotientGroup.mk (spike (0 : ℕ) i)) = 0 := by
  obtain ⟨s, N, fbar, hfactor⟩ :=
    ContinuousMap.exists_finset_openNormalSubgroup_pi_factor (identityLabel (0 : ℕ) 1)
  let : Finite s := inferInstance
  let : Finite (C₂ ⧸ N.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
  let : DiscreteTopology (C₂ ⧸ N.toSubgroup) := QuotientGroup.discreteTopology N.isOpen
  refine ⟨s, N, fbar, hfactor, inferInstance, inferInstance, ?_, ?_⟩
  · exact (hfactor (1 : ℕ → C₂)).trans (by decide)
  · exact (hfactor (spike (0 : ℕ))).trans (by decide)

-- A constant observer has an explicit empty-coordinate factorization, with
-- no compactness or discreteness assumptions.
example {I : Type u} {G : Type v} {Y : Type*} [Group G] [TopologicalSpace G]
    [TopologicalSpace Y] (y : Y) :
    ∃ (N : OpenNormalSubgroup G)
      (fbar : C(((∅ : Finset I) → G ⧸ N.toSubgroup), Y)),
      ∀ x : I → G,
        fbar (fun i : (∅ : Finset I) => QuotientGroup.mk (x i)) =
          ContinuousMap.const (I → G) y x := by
  let N : OpenNormalSubgroup G := { toSubgroup := ⊤, isOpen' := isOpen_univ }
  exact ⟨N, ContinuousMap.const _ y, fun _ => rfl⟩

-- An empty-index power is a singleton, not an empty type.
example {G : Type u} {Y : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace Y] (f : C((Empty → G), Y)) (x : Empty → G) :
    f x = f (fun _ => 1) := by
  have hx : x = (fun _ => 1) := by
    funext i
    cases i
  exact congrArg f hx

-- Every group power is inhabited, even when the index is empty.
example {I : Type u} {G : Type v} [Group G] [TopologicalSpace G] :
    IsEmpty C((I → G), Empty) :=
  ⟨fun f => Empty.elim (f (fun _ => 1))⟩

end GroupTheoryTest.Topology.Algebra.CompactGroup.PiDiscreteFactor
