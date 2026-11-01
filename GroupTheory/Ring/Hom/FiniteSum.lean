/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite sums of orthogonal ring homomorphisms

A finite family of nonunital ring homomorphisms with mutually annihilating images
has a sum. Its underlying additive homomorphism is the usual finite sum of
`AddMonoidHom`s; no addition on arbitrary `NonUnitalRingHom`s is required.

For a finite dependent product, orthogonality of the images of the units implies
orthogonality of the whole component images when the target is associative.
If those unit images sum to one, `Pi.liftRingHom` is the unique unital ring
homomorphism extending the components along the zero-off functions `Pi.single`.
The unit images need only centralize the image of this map, not the whole target.

## References

This construction uses Mathlib's additive finite sums and its Hom and Pi APIs.
The prior formalizations include work by Patrick Massot, Kevin Buzzard,
Kim Morrison, Johan Commelin, Chris Hughes, Johannes Hölzl, Yury Kudryashov,
Amelia Livingston, Jireh Loreaux, Simon Hudon and Eric Wieser.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped BigOperators

namespace NonUnitalRingHom

variable {ι : Type u} {R : Type v} {S : Type w}
variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- The sum of finitely many nonunital ring homomorphisms whose distinct images
annihilate one another, in both orders. The source and target need not be unital
or multiplicatively associative. -/
public def sum (s : Finset ι) (f : ι → R →ₙ+* S)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y : R, f i x * f j y = 0) : R →ₙ+* S := by
  classical
  refine
    { toAddMonoidHom := ∑ i ∈ s, (f i).toAddMonoidHom
      map_mul' := ?_ }
  intro x y
  change (∑ i ∈ s, (f i).toAddMonoidHom) (x * y) =
    (∑ i ∈ s, (f i).toAddMonoidHom) x * (∑ i ∈ s, (f i).toAddMonoidHom) y
  have hsum (z : R) :
      (∑ i ∈ s, (f i).toAddMonoidHom) z = ∑ i ∈ s, f i z :=
    map_sum (AddMonoidHom.eval z) (fun i => (f i).toAddMonoidHom) s
  simp only [hsum]
  symm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  calc
    ∑ j ∈ s, f i x * f j y = f i x * f i y :=
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => h i hi j hj hji.symm x y)
    _ = f i (x * y) := (map_mul (f i) x y).symm

/-- The additive homomorphism underlying an orthogonal sum is exactly the stock
finite sum of the underlying additive homomorphisms. -/
@[simp]
theorem sum_toAddMonoidHom (s : Finset ι) (f : ι → R →ₙ+* S)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y : R, f i x * f j y = 0) :
    (sum s f h).toAddMonoidHom = ∑ i ∈ s, (f i).toAddMonoidHom := rfl

/-- Evaluation of an orthogonal sum is the finite sum of the component values. -/
@[simp]
theorem sum_apply (s : Finset ι) (f : ι → R →ₙ+* S)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x y : R, f i x * f j y = 0) (x : R) :
    sum s f h x = ∑ i ∈ s, f i x :=
  map_sum (AddMonoidHom.eval x) (fun i => (f i).toAddMonoidHom) s

@[simp]
theorem sum_empty (f : ι → R →ₙ+* S)
    (h : ∀ i ∈ (∅ : Finset ι), ∀ j ∈ (∅ : Finset ι), i ≠ j →
      ∀ x y : R, f i x * f j y = 0) :
    sum ∅ f h = 0 := by
  ext x
  simp

@[simp]
theorem sum_singleton (i : ι) (f : ι → R →ₙ+* S)
    (h : ∀ j ∈ ({i} : Finset ι), ∀ k ∈ ({i} : Finset ι), j ≠ k →
      ∀ x y : R, f j x * f k y = 0) :
    sum {i} f h = f i := by
  ext x
  simp

end NonUnitalRingHom

namespace Pi

variable {ι : Type u} {R : ι → Type v} {S : Type w}
variable [∀ i, NonAssocSemiring (R i)] [Semiring S]

variable [Fintype ι]

/-- The unital ring homomorphism out of a finite dependent product associated to
nonunital component maps with orthogonal unit images summing to one.
The component semirings need not be multiplicatively associative. -/
public def liftRingHom (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) : (∀ i, R i) →+* S := by
  classical
  have hcross (i j : ι) (hij : i ≠ j) (x : R i) (y : R j) :
      φ i x * φ j y = 0 := by
    have hi : φ i x * φ i 1 = φ i x := by rw [← map_mul, mul_one]
    have hj : φ j 1 * φ j y = φ j y := by rw [← map_mul, one_mul]
    calc
      φ i x * φ j y = (φ i x * φ i 1) * (φ j 1 * φ j y) := by rw [hi, hj]
      _ = φ i x * (φ i 1 * φ j 1) * φ j y := by simp only [mul_assoc]
      _ = 0 := by rw [horth i j hij, mul_zero, zero_mul]
  let ψ : (∀ i, R i) →ₙ+* S := NonUnitalRingHom.sum Finset.univ
    (fun i => (φ i).comp (Pi.evalNonUnitalRingHom R i))
    (fun i _ j _ hij x y => hcross i j hij (x i) (y j))
  exact
    { toFun := ψ
      map_zero' := map_zero ψ
      map_add' := map_add ψ
      map_mul' := map_mul ψ
      map_one' := by
        calc
          ψ (1 : ∀ i, R i) = ∑ i, φ i 1 :=
            map_sum (AddMonoidHom.eval (1 : ∀ i, R i))
              (fun i => ((φ i).comp (Pi.evalNonUnitalRingHom R i)).toAddMonoidHom)
              Finset.univ
          _ = 1 := hone }

/-- Evaluation of the lift is the sum of the component values. -/
@[simp]
theorem liftRingHom_apply (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) (x : ∀ i, R i) :
    liftRingHom φ horth hone x = ∑ i, φ i (x i) := by
  classical
  change (∑ i, ((φ i).comp (Pi.evalNonUnitalRingHom R i)).toAddMonoidHom) x =
    ∑ i, φ i (x i)
  exact map_sum (AddMonoidHom.eval x)
    (fun i => ((φ i).comp (Pi.evalNonUnitalRingHom R i)).toAddMonoidHom) Finset.univ

variable [DecidableEq ι]

/-- Restricting the lift to the zero-off insertion at a coordinate recovers the
corresponding nonunital component map. -/
theorem liftRingHom_single (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) (i : ι) (x : R i) :
    liftRingHom φ horth hone (Pi.single i x) = φ i x := by
  rw [liftRingHom_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j _ hji
    simp [hji]

/-- A unital ring homomorphism from the finite product is determined by its
restrictions to the nonunital zero-off coordinate insertions. In particular,
extending the restrictions of such a homomorphism recovers that homomorphism. -/
theorem liftRingHom_unique (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) (g : (∀ i, R i) →+* S)
    (hg : ∀ i (x : R i), g (Pi.single i x) = φ i x) :
    g = liftRingHom φ horth hone := by
  ext x
  have hx : (∑ i, Pi.single i (x i)) = x := by
    ext i
    have hsum := map_sum (Pi.evalNonUnitalRingHom R i)
      (fun j => Pi.single j (x j)) Finset.univ
    simp only [Pi.evalNonUnitalRingHom_apply] at hsum
    rw [hsum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hji
      simp [hji]
  calc
    g x = g (∑ i, Pi.single i (x i)) := congrArg g hx.symm
    _ = ∑ i, g (Pi.single i (x i)) := map_sum g _ _
    _ = ∑ i, φ i (x i) := Finset.sum_congr rfl (fun i _ => hg i (x i))
    _ = liftRingHom φ horth hone x := (liftRingHom_apply φ horth hone x).symm

/-- The lift and restriction operations are inverse: equality with a lift is
equivalent to having the prescribed zero-off coordinate restrictions. -/
@[simp]
theorem liftRingHom_eq_iff (φ : ∀ i, R i →ₙ+* S)
    (horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0)
    (hone : ∑ i, φ i 1 = 1) (g : (∀ i, R i) →+* S) :
    liftRingHom φ horth hone = g ↔ ∀ i (x : R i), g (Pi.single i x) = φ i x := by
  constructor
  · intro h i x
    rw [← h, liftRingHom_single]
  · intro hg
    exact (liftRingHom_unique φ horth hone g hg).symm

end Pi
