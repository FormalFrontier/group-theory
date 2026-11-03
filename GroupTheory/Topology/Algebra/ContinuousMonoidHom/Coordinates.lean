/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Separation.Basic

/-!
# Coordinates and tails of homomorphisms on products

Coordinate insertion and finite truncation use only the unit laws in the factors.
For a globally continuous multiplicative unital map to a T₀ unital magma, trivial
coordinate maps annihilate the entire complementary tail, not just finite supports.
No continuity of multiplication or associativity is required.

The coordinate insertions and product-topology API are from Mathlib. The pure
truncation calculus follows the product-decomposition formalization in this library.
-/

@[expose] public section

open Filter Topology

attribute [local instance] Classical.propDecidable

universe u v w

variable {ι : Type u} {G : ι → Type v} {D : Type w}

namespace MonoidHom

variable [∀ i, MulOneClass (G i)] [MulOneClass D]

/-- The restriction of a homomorphism on a product to one coordinate. -/
noncomputable def coordinateHom (f : (∀ i, G i) →* D) (i : ι) : G i →* D := by
  classical
  exact f.comp (MonoidHom.mulSingle G i)

@[simp]
theorem coordinateHom_apply (f : (∀ i, G i) →* D) (i : ι) (x : G i) :
    f.coordinateHom i x = f (Pi.mulSingle i x) := by
  classical
  rfl

/-- A coordinate map is nontrivial exactly when some coordinate insertion has
nontrivial image. -/
theorem coordinateHom_ne_one_iff (f : (∀ i, G i) →* D) (i : ι) :
    f.coordinateHom i ≠ 1 ↔ ∃ x, f (Pi.mulSingle i x) ≠ 1 := by
  classical
  simp only [ne_eq, DFunLike.ext_iff, coordinateHom_apply, MonoidHom.one_apply, not_forall]

/-- Restriction to a coordinate preserves continuity for the product topology. -/
theorem continuous_coordinateHom [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]
    (f : (∀ i, G i) →* D) (hf : Continuous f) (i : ι) :
    Continuous (f.coordinateHom i) := by
  classical
  exact (hf.comp' (continuous_mulSingle (A := G) i)).congr
    (fun x => (coordinateHom_apply f i x).symm)

/-- Agreement on individual coordinates gives agreement on each finite truncation.
The induction uses only unit laws, not associativity. -/
theorem map_coordinate_truncation_eq (f g : (∀ i, G i) →* D)
    (s : Finset ι) (x : ∀ i, G i)
    (h : ∀ i ∈ s, f (Pi.mulSingle i (x i)) = g (Pi.mulSingle i (x i))) :
    f (fun i => if i ∈ s then x i else 1) =
      g (fun i => if i ∈ s then x i else 1) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      have he : (fun i => if i ∈ (∅ : Finset ι) then x i else 1) = (1 : ∀ i, G i) := by
        funext i
        simp
      rw [he]
      exact (map_one f).trans (map_one g).symm
  | @insert i s hi ih =>
      intro h
      have htrunc : (fun j => if j ∈ insert i s then x j else 1) =
          Pi.mulSingle i (x i) * (fun j => if j ∈ s then x j else 1) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [hi]
        · simp [hji]
      rw [htrunc, map_mul, map_mul, h i (Finset.mem_insert_self i s),
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- Retain the coordinates in a finite set and replace all other coordinates by one. -/
noncomputable def coordinateTruncation (s : Finset ι) : (∀ i, G i) →* ∀ i, G i :=
  MonoidHom.pi fun i => if i ∈ s then Pi.evalMonoidHom G i else 1

@[simp]
theorem coordinateTruncation_apply (s : Finset ι) (x : ∀ i, G i) :
    coordinateTruncation s x = fun i => if i ∈ s then x i else 1 := by
  funext i
  by_cases hi : i ∈ s <;> simp [coordinateTruncation, hi]

/-- Replace the coordinates in a finite set by one and retain all other coordinates. -/
noncomputable def coordinateTail (s : Finset ι) : (∀ i, G i) →* ∀ i, G i :=
  MonoidHom.pi fun i => if i ∈ s then 1 else Pi.evalMonoidHom G i

@[simp]
theorem coordinateTail_apply (s : Finset ι) (x : ∀ i, G i) :
    coordinateTail s x = fun i => if i ∈ s then 1 else x i := by
  funext i
  by_cases hi : i ∈ s <;> simp [coordinateTail, hi]

/-- A product element is its finite truncation times its complementary tail. -/
theorem coordinateTruncation_mul_coordinateTail (s : Finset ι) (x : ∀ i, G i) :
    coordinateTruncation s x * coordinateTail s x = x := by
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- On a constant family, finite truncation is Mathlib's multiplicative indicator. -/
theorem coordinateTruncation_eq_mulIndicatorHom {A : Type v} [MulOneClass A]
    (s : Finset ι) :
    coordinateTruncation (G := fun _ : ι => A) s = Set.mulIndicatorHom A (s : Set ι) := by
  ext x i
  by_cases hi : i ∈ s <;> simp [Set.mulIndicatorHom, hi]

section Topology

variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- Finite truncations converge to the original element in the product topology. -/
theorem tendsto_coordinateTruncation (x : ∀ i, G i) :
    Tendsto (fun s : Finset ι => coordinateTruncation s x) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s :=
    eventually_atTop.mpr ⟨{i}, fun s hs => hs (Finset.mem_singleton_self i)⟩
  exact tendsto_const_nhds.congr' (hi.mono fun s hs => by simp [hs])

/-- Complementary tails converge to one in the product topology. -/
theorem tendsto_coordinateTail (x : ∀ i, G i) :
    Tendsto (fun s : Finset ι => coordinateTail s x) atTop (𝓝 (1 : ∀ i, G i)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s :=
    eventually_atTop.mpr ⟨{i}, fun s hs => hs (Finset.mem_singleton_self i)⟩
  exact tendsto_const_nhds.congr' (hi.mono fun s hs => by simp [hs])

/-- If every coordinate value of a point has trivial image, then so does the point. -/
theorem eq_one_of_coordinate_values_eq_one [T0Space D]
    (f : (∀ i, G i) →* D) (hf : Continuous f) (x : ∀ i, G i)
    (hx : ∀ i, f.coordinateHom i (x i) = 1) : f x = 1 := by
  have htrunc (s : Finset ι) : f (coordinateTruncation s x) = 1 := by
    have h := map_coordinate_truncation_eq f (1 : (∀ i, G i) →* D) s x
      (fun i _ => by simpa only [coordinateHom_apply, one_apply] using hx i)
    simpa only [coordinateTruncation_apply, one_apply] using h
  have htail (s : Finset ι) : f (coordinateTail s x) = f x := by
    have h : f (coordinateTruncation s x) * f (coordinateTail s x) = f x := by
      rw [← map_mul, coordinateTruncation_mul_coordinateTail]
    simpa only [htrunc s, one_mul] using h
  have hforward : (1 : D) ⤳ f x := by
    apply specializes_iff_forall_open.mpr
    intro U hU hxU
    have hlim : Tendsto (fun s : Finset ι => f (coordinateTruncation s x))
        atTop (𝓝 (f x)) :=
      Filter.Tendsto.congr
        (f₁ := f ∘ fun s : Finset ι => coordinateTruncation s x)
        (f₂ := fun s : Finset ι => f (coordinateTruncation s x))
        (fun _ => rfl) ((hf.tendsto x).comp (tendsto_coordinateTruncation x))
    obtain ⟨s, hs⟩ :=
      ((tendsto_iff_forall_eventually_mem.mp hlim) U (hU.mem_nhds hxU)).exists
    simpa only [htrunc s] using hs
  have hbackward : f x ⤳ (1 : D) := by
    apply specializes_iff_forall_open.mpr
    intro U hU hUone
    have hlim : Tendsto (fun s : Finset ι => f (coordinateTail s x)) atTop (𝓝 (1 : D)) := by
      simpa only [map_one] using
        (Filter.Tendsto.congr
          (f₁ := f ∘ fun s : Finset ι => coordinateTail s x)
          (f₂ := fun s : Finset ι => f (coordinateTail s x))
          (fun _ => rfl) ((hf.tendsto (1 : ∀ i, G i)).comp (tendsto_coordinateTail x)))
    obtain ⟨s, hs⟩ :=
      ((tendsto_iff_forall_eventually_mem.mp hlim) U (hU.mem_nhds hUone)).exists
    simpa only [htail s] using hs
  exact (inseparable_iff_specializes_and.mpr ⟨hbackward, hforward⟩).eq

/-- A globally continuous homomorphism to a T₀ unital magma kills an element
which is one on a finite set whenever its coordinate maps outside that set are trivial.
Both specialization directions are needed; no uniqueness of arbitrary limits in a
T₀ space is used. -/
theorem eq_one_of_coordinates_eq_one [T0Space D] (f : (∀ i, G i) →* D)
    (hf : Continuous f) (s : Finset ι) (hs : ∀ i, i ∉ s → f.coordinateHom i = 1)
    (x : ∀ i, G i) (hx : ∀ i ∈ s, x i = 1) : f x = 1 := by
  apply eq_one_of_coordinate_values_eq_one f hf x
  intro i
  by_cases hi : i ∈ s
  · rw [hx i hi, map_one]
  · rw [hs i hi, one_apply]

/-- Trivial coordinate maps determine the trivial globally continuous homomorphism
when the target is T₀. -/
theorem eq_one_of_coordinateHom_eq_one [T0Space D] (f : (∀ i, G i) →* D)
    (hf : Continuous f) (h : ∀ i, f.coordinateHom i = 1) : f = 1 := by
  ext x
  exact f.eq_one_of_coordinates_eq_one hf ∅ (fun i _ => h i) x (by simp)

end Topology

end MonoidHom

namespace ContinuousMonoidHom

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- Evaluation at a coordinate as a continuous homomorphism. -/
def coordinateProjection (i : ι) : (∀ j, G j) →ₜ* G i :=
  { toFun := fun x => x i
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    continuous_toFun := continuous_apply i }

@[simp]
theorem coordinateProjection_apply (i : ι) (x : ∀ j, G j) :
    coordinateProjection (G := G) i x = x i := rfl

/-- Restriction of a continuous product homomorphism to one coordinate, by
inserting the identity in every other coordinate. -/
noncomputable def coordinateHom (f : (∀ i, G i) →ₜ* D) (i : ι) : G i →ₜ* D := by
  classical
  exact f.comp
    { toFun := Pi.mulSingle i
      map_one' := by
        funext j
        simp
      map_mul' := by
        intro x y
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [h]
      continuous_toFun := by
        apply continuous_pi
        intro j
        by_cases h : j = i
        · subst j
          have he : (fun x : G i => Pi.mulSingle i x i) = (fun x : G i => x) := by
            funext x
            simp
          rw [he]
          exact continuous_id
        · have he : (fun x : G i => Pi.mulSingle i x j) = (fun _ : G i => (1 : G j)) := by
            funext x
            simp [h]
          rw [he]
          exact continuous_const }

@[simp]
theorem coordinateHom_apply (f : (∀ i, G i) →ₜ* D) (i : ι) (t : G i) :
    f.coordinateHom i t = f (Pi.mulSingle i t) := rfl

@[simp]
theorem coordinateHom_one (i : ι) :
    (1 : (∀ i, G i) →ₜ* D).coordinateHom i = 1 := by
  apply DFunLike.ext
  intro t
  rfl

/-- The continuous coordinate restriction has the ordinary coordinate map as its
underlying unital multiplicative map. -/
theorem toMonoidHom_coordinateHom (f : (∀ i, G i) →ₜ* D) (i : ι) :
    (f.coordinateHom i).toMonoidHom = f.toMonoidHom.coordinateHom i := by
  ext x
  rfl

end Monoid

section CommMonoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [CommMonoid D] [TopologicalSpace D] [ContinuousMul D]

/-- Extend a coordinate homomorphism to the product by precomposition with
coordinate projection, expressed with additive type tags. -/
def coordinateContribution (i : ι) :
    Additive (G i →ₜ* D) →+ Additive ((∀ j, G j) →ₜ* D) :=
  { toFun := fun g => Additive.ofMul (g.toMul.comp (coordinateProjection i))
    map_zero' := by
      change (1 : G i →ₜ* D).comp (coordinateProjection i) = 1
      apply DFunLike.ext
      intro x
      rfl
    map_add' := by
      intro f g
      change (f.toMul * g.toMul).comp (coordinateProjection i) =
        f.toMul.comp (coordinateProjection i) * g.toMul.comp (coordinateProjection i)
      apply DFunLike.ext
      intro x
      rfl }

theorem coordinateContribution_apply (i : ι) (g : Additive (G i →ₜ* D)) :
    coordinateContribution (G := G) (D := D) i g =
      Additive.ofMul (g.toMul.comp (coordinateProjection i)) := rfl

@[simp]
theorem coordinateContribution_apply_apply (i : ι) (g : Additive (G i →ₜ* D))
    (x : ∀ j, G j) :
    (coordinateContribution (G := G) (D := D) i g).toMul x = g.toMul (x i) := rfl

/-- Restricting a coordinate contribution to its own coordinate recovers the map. -/
theorem coordinateHom_coordinateContribution (i : ι) (g : G i →ₜ* D) :
    ((coordinateContribution (G := G) (D := D) i (Additive.ofMul g)).toMul).coordinateHom i =
      g := by
  ext x
  simp

end CommMonoid

end ContinuousMonoidHom
