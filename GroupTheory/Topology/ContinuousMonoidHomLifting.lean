/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Homomorphic lifts through covering maps

A normalized continuous lift through a covering monoid homomorphism preserves
multiplication when right translations on the source and covering space are continuous.
The comparison fixes the right factor and applies covering uniqueness at the unit;
it needs only a preconnected source, not associativity or joint multiplication continuity.
Postcomposition is also injective on continuous monoid homomorphisms from a
preconnected source, without any translation-continuity assumption.

For a simply connected, locally path connected monoid, `IsCoveringMap.liftContinuousMonoidHom`
bundles the existing normalized continuous-map lift, storing that same map as its function.
Its characteristic API identifies every normalized continuous lift and gives existence
and uniqueness of a homomorphic lift. All three spaces retain their given structures.

In additive notation, the covering from ℝ × ℕ to (ℝ / ℤ) × ℕ and the lift
s ↦ (s, 0) from ℝ≥0 illustrate the monoid generality and a nontrivial covering kernel.
Integral translates are lifts but are not normalized. For a disconnected source ℤ,
the normalized lift n ↦ (n², 0) of the zero map is not additive, so connectedness
cannot simply be dropped from the given-lift assertion. These are mathematical
illustrations, not additional hypotheses.

## References

The topological existence and uniqueness ingredients and their formalization are
Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts` in
`Mathlib.Topology.Homotopy.Lifting` and `IsCoveringMap.eq_of_comp_eq` in
`Mathlib.Topology.Covering.Basic`. The fixed-right-translation argument here combines
those public results with Mathlib's continuous-map and monoid-homomorphism APIs.
-/

@[expose] public section

universe u v w

namespace IsCoveringMap

/-- A supplied normalized continuous lift through a covering homomorphism
preserves multiplication, using only continuous right translations. -/
theorem map_mul_of_normalized_lift
    {X : Type u} {E : Type v} {B : Type w}
    [MulOneClass X] [MulOneClass E] [MulOne B]
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    [PreconnectedSpace X]
    {p : E →* B} (hp : IsCoveringMap p) (f : X →* B)
    (L : C(X, E)) (hL1 : L 1 = 1)
    (hL : (p : E → B) ∘ (L : X → E) = (f : X → B))
    (hXr : ∀ y : X, Continuous (fun x : X => x * y))
    (hEr : ∀ z : E, Continuous (fun e : E => e * z)) :
    ∀ x y : X, L (x * y) = L x * L y := by
  intro x y
  have hLp : ∀ t : X, p (L t) = f t := fun t => congrFun hL t
  have heq : (fun t : X => L (t * y)) = (fun t : X => L t * L y) :=
    hp.eq_of_comp_eq
      ((ContinuousMap.continuous L).comp (hXr y))
      ((hEr (L y)).comp (ContinuousMap.continuous L))
      (by
        funext t
        simp only [Function.comp_apply]
        rw [hLp (t * y), map_mul f t y, map_mul p (L t) (L y),
          hLp t, hLp y])
      (1 : X)
      (by simp only [one_mul, hL1])
  exact congrFun heq x

/-- Postcomposition by a covering continuous monoid homomorphism is
injective on continuous monoid homomorphisms with preconnected source. -/
theorem continuousMonoidHom_comp_injective
    {X : Type u} {E : Type v} {B : Type w}
    [Monoid X] [Monoid E] [Monoid B]
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
    [PreconnectedSpace X]
    (p : E →ₜ* B) (hp : IsCoveringMap p) :
    Function.Injective (fun g : X →ₜ* E => p.comp g) := by
  intro g h hgh
  have hg : Continuous (g : X → E) := ContinuousMap.continuous g.toContinuousMap
  have hh : Continuous (h : X → E) := ContinuousMap.continuous h.toContinuousMap
  have hcomp : (p : E → B) ∘ (g : X → E) =
      (p : E → B) ∘ (h : X → E) :=
    (ContinuousMonoidHom.coe_comp p g).symm.trans
      ((congrArg (fun k : X →ₜ* B => (k : X → B)) hgh).trans
        (ContinuousMonoidHom.coe_comp p h))
  have heq : (g : X → E) = (h : X → E) :=
    hp.eq_of_comp_eq hg hh hcomp (1 : X)
      ((map_one g).trans (map_one h).symm)
  exact ContinuousMonoidHom.ext (fun x => congrFun heq x)

section

variable {X : Type u} {E : Type v} {B : Type w}
variable [Monoid X] [Monoid E] [Monoid B]
variable [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace B]
variable [hSC : SimplyConnectedSpace X] [hLPC : LocallyPathConnectedSpace X]

/-- The normalized homomorphic lift, storing the existing continuous lift itself. -/
noncomputable def liftContinuousMonoidHom
    (p : E →ₜ* B) (hp : IsCoveringMap p) (f : X →ₜ* B)
    (hXr : ∀ y : X, Continuous (fun x : X => x * y))
    (hEr : ∀ z : E, Continuous (fun e : E => e * z)) : X →ₜ* E :=
  let ex : ∃! F : C(X, E),
      F 1 = 1 ∧ (p : E → B) ∘ (F : X → E) = (f : X → B) :=
    hp.existsUnique_continuousMap_lifts f.toContinuousMap 1 1
      ((map_one p).trans (map_one f).symm)
  let L : C(X, E) := Classical.choose ex
  let hL : L 1 = 1 ∧ (p : E → B) ∘ (L : X → E) = (f : X → B) :=
    (Classical.choose_spec ex).1
  { toContinuousMap := L
    map_one' := hL.1
    map_mul' := IsCoveringMap.map_mul_of_normalized_lift
      (p := p.toMonoidHom) hp f.toMonoidHom L hL.1 hL.2 hXr hEr }

variable (p : E →ₜ* B) (hp : IsCoveringMap p) (f : X →ₜ* B)
variable (hXr : ∀ y : X, Continuous (fun x : X => x * y))
variable (hEr : ∀ z : E, Continuous (fun e : E => e * z))

/-- Forgetting the homomorphism structure returns the very same chosen continuous map. -/
theorem liftContinuousMonoidHom_toContinuousMap :
    (liftContinuousMonoidHom p hp f hXr hEr).toContinuousMap =
      Classical.choose
        (hp.existsUnique_continuousMap_lifts f.toContinuousMap 1 1
          ((map_one p).trans (map_one f).symm)) := by
  rfl

/-- The stored function is exactly the existing normalized continuous-map choice. -/
theorem coe_liftContinuousMonoidHom :
    (liftContinuousMonoidHom p hp f hXr hEr : X → E) =
      ((Classical.choose
        (hp.existsUnique_continuousMap_lifts f.toContinuousMap 1 1
          ((map_one p).trans (map_one f).symm)) : C(X, E)) : X → E) := by
  rfl

/-- Every normalized continuous lift is the stored continuous map. -/
theorem continuousMap_eq_liftContinuousMonoidHom_iff (g : C(X, E)) :
    g = (liftContinuousMonoidHom p hp f hXr hEr).toContinuousMap ↔
      g 1 = 1 ∧ (p : E → B) ∘ (g : X → E) = (f : X → B) := by
  rw [liftContinuousMonoidHom_toContinuousMap]
  have hchoice := Classical.choose_spec
    (hp.existsUnique_continuousMap_lifts f.toContinuousMap 1 1
      ((map_one p).trans (map_one f).symm))
  constructor
  · intro hg
    exact hg.symm ▸ hchoice.1
  · intro hg
    exact hchoice.2 g hg

/-- The normalized homomorphic lift satisfies the original commuting triangle. -/
theorem comp_liftContinuousMonoidHom :
    p.comp (liftContinuousMonoidHom p hp f hXr hEr) = f := by
  apply ContinuousMonoidHom.ext
  intro x
  have hnorm := (continuousMap_eq_liftContinuousMonoidHom_iff p hp f hXr hEr
    (liftContinuousMonoidHom p hp f hXr hEr).toContinuousMap).1 rfl
  exact (congrFun
    (ContinuousMonoidHom.coe_comp p (liftContinuousMonoidHom p hp f hXr hEr)) x).trans
    (congrFun hnorm.2 x)

/-- The commuting triangle evaluated at a source point. -/
theorem apply_liftContinuousMonoidHom (x : X) :
    p (liftContinuousMonoidHom p hp f hXr hEr x) = f x := by
  have hx := congrArg (fun g : X →ₜ* B => g x)
    (comp_liftContinuousMonoidHom p hp f hXr hEr)
  simpa only [ContinuousMonoidHom.coe_comp, Function.comp_apply] using hx

/-- A continuous monoid homomorphism is the lift exactly when its triangle commutes. -/
theorem eq_liftContinuousMonoidHom_iff (g : X →ₜ* E) :
    g = liftContinuousMonoidHom p hp f hXr hEr ↔ p.comp g = f := by
  constructor
  · intro hg
    exact hg.symm ▸ comp_liftContinuousMonoidHom p hp f hXr hEr
  · intro hg
    exact continuousMonoidHom_comp_injective p hp
      (hg.trans (comp_liftContinuousMonoidHom p hp f hXr hEr).symm)

include hSC hLPC hp hXr hEr in
/-- Existence and uniqueness follow from the constructed lift and its characteristic API. -/
theorem existsUnique_continuousMonoidHom_lifts :
    ∃! g : X →ₜ* E, p.comp g = f := by
  exact ⟨liftContinuousMonoidHom p hp f hXr hEr,
    comp_liftContinuousMonoidHom p hp f hXr hEr,
    fun g hg => (eq_liftContinuousMonoidHom_iff p hp f hXr hEr g).2 hg⟩

/-- Changing the covering and right-continuity proofs does not change the lift. -/
theorem liftContinuousMonoidHom_proof_independent
    (hp' : IsCoveringMap p)
    (hXr' : ∀ y : X, Continuous (fun x : X => x * y))
    (hEr' : ∀ z : E, Continuous (fun e : E => e * z)) :
    liftContinuousMonoidHom p hp f hXr hEr =
      liftContinuousMonoidHom p hp' f hXr' hEr' := by
  exact (eq_liftContinuousMonoidHom_iff p hp' f hXr' hEr'
    (liftContinuousMonoidHom p hp f hXr hEr)).2
      (comp_liftContinuousMonoidHom p hp f hXr hEr)

end

end IsCoveringMap
