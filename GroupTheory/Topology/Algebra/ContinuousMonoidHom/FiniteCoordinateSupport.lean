/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Coordinates
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups

/-!
# Dependence on coordinates and coordinate values

A function that depends only on the coordinates in a set and takes `1` to `1` is trivial
on every single-coordinate insertion outside that set. For a globally continuous
homomorphism into a `T0` space, triviality of all coordinate values outside a set is
equivalent to determination by that set. Coordinate support records the nontrivial
coefficient homomorphisms. Groups with no small subgroups and continuous
fixed left translations satisfy the required separation property.
-/

@[expose] public section

universe u v w

namespace Function

/-- If a function takes `1` to `1` and its value is determined by the coordinates in `S`,
then it takes every single-coordinate insertion outside `S` to `1`. -/
theorem apply_mulSingle_eq_one_of_eqOn {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, One (G i)] [One D] [DecidableEq ι]
    (f : (∀ i, G i) → D) (hf1 : f 1 = 1) (S : Set ι)
    (hdep : ∀ x y : (∀ i, G i), (∀ i ∈ S, x i = y i) → f x = f y)
    {i : ι} (hi : i ∉ S) (a : G i) : f (Pi.mulSingle i a) = 1 := by
  calc
    f (Pi.mulSingle i a) = f (Pi.mulSingle i (1 : G i)) := by
      apply hdep
      intro j hj
      have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      exact (Pi.mulSingle_eq_of_ne hji a).trans
        (Pi.mulSingle_eq_of_ne hji (1 : G i)).symm
    _ = f 1 := congrArg f (Pi.mulSingle_one i)
    _ = 1 := hf1

end Function

namespace MonoidHom

section

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, MulOneClass (G i)] [MulOneClass D]
variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- For a continuous homomorphism into a `T0` space, triviality of every coefficient value
outside `S` is equivalent to determination by the coordinates in `S`. The set `S` need not
be finite. -/
theorem coordinate_values_eq_one_off_iff [T0Space D]
    (f : (∀ i, G i) →* D) (hf : Continuous f) (S : Set ι) :
    (∀ i, i ∉ S → ∀ a : G i, f.coordinateHom i a = 1) ↔
      (∀ x y : (∀ i, G i), (∀ i ∈ S, x i = y i) → f x = f y) := by
  classical
  constructor
  · intro hcoeff x y hxy
    let q : ∀ i, G i := fun i => if i ∈ S then x i else 1
    let tx : ∀ i, G i := fun i => if i ∈ S then 1 else x i
    let ty : ∀ i, G i := fun i => if i ∈ S then 1 else y i
    -- A tuple equal to one on `S` has trivial coefficient values everywhere.
    have htail (t : ∀ i, G i) (ht : ∀ i ∈ S, t i = 1) : f t = 1 := by
      apply eq_one_of_coordinate_values_eq_one f hf t
      intro i
      by_cases hi : i ∈ S
      · rw [ht i hi]
        exact (f.coordinateHom i).map_one
      · exact hcoeff i hi (t i)
    have htx : f tx = 1 := htail tx (by
      intro i hi
      simp only [tx, ite_eq_left hi])
    have hty : f ty = 1 := htail ty (by
      intro i hi
      simp only [ty, ite_eq_left hi])
    have hx : x = q * tx := by
      funext i
      by_cases hi : i ∈ S
      · simp only [Pi.mul_apply, q, tx, ite_eq_left hi, mul_one]
      · simp only [Pi.mul_apply, q, tx, ite_eq_right hi, one_mul]
    have hy : y = q * ty := by
      funext i
      by_cases hi : i ∈ S
      · simpa only [Pi.mul_apply, q, ty, ite_eq_left hi, mul_one] using (hxy i hi).symm
      · simp only [Pi.mul_apply, q, ty, ite_eq_right hi, one_mul]
    calc
      f x = f (q * tx) := congrArg f hx
      _ = f q * f tx := f.map_mul q tx
      _ = f q := by rw [htx, mul_one]
      _ = f q * f ty := by rw [hty, mul_one]
      _ = f (q * ty) := (f.map_mul q ty).symm
      _ = f y := (congrArg f hy).symm
  · intro hdep i hi a
    calc
      f.coordinateHom i a = f (Pi.mulSingle i a) := coordinateHom_apply f i a
      _ = 1 :=
        Function.apply_mulSingle_eq_one_of_eqOn (fun z => f z) f.map_one S hdep hi a

end

section

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, MulOneClass (G i)] [Group D]
variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]
variable [ContinuousConstSMul D D] [NoSmallSubgroups D]

/-- For a globally continuous homomorphism into a group with no small subgroups and
continuous fixed left translations, triviality of every coefficient value outside `S`
is equivalent to determination by `S`. No additional separation hypothesis is needed. -/
theorem coordinate_values_eq_one_off_iff_of_noSmallSubgroups
    (f : (∀ i, G i) →* D) (hf : Continuous f) (S : Set ι) :
    (∀ i, i ∉ S → ∀ a : G i, f.coordinateHom i a = 1) ↔
      (∀ x y : (∀ i, G i), (∀ i ∈ S, x i = y i) → f x = f y) := by
  let _ : T0Space D := NoSmallSubgroups.t0Space
  exact coordinate_values_eq_one_off_iff f hf S

end

end MonoidHom


namespace MonoidHom

section

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, MulOneClass (G i)] [MulOneClass D]
variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- Two globally continuous homomorphisms into a `T0` space agree if their coordinate
homomorphisms agree and every coefficient value of the first map outside a finite set
is one. Triviality outside the same set for the second map follows from this agreement. -/
theorem ext_of_coordinateHom_eq_of_eq_one_off_finset [T0Space D]
    (f g : (∀ i, G i) →* D) (hf : Continuous f) (hg : Continuous g)
    (s : Finset ι)
    (hfout : ∀ i, i ∉ s → ∀ a : G i, f.coordinateHom i a = 1)
    (heq : ∀ i, f.coordinateHom i = g.coordinateHom i) : f = g := by
  classical
  have hgout : ∀ i, i ∉ s → ∀ a : G i, g.coordinateHom i a = 1 := by
    intro i hi a
    calc
      g.coordinateHom i a = f.coordinateHom i a :=
        (congrArg (fun c : G i →* D => c a) (heq i)).symm
      _ = 1 := hfout i hi a
  have hdep_f := (coordinate_values_eq_one_off_iff f hf (s : Set ι)).mp hfout
  have hdep_g := (coordinate_values_eq_one_off_iff g hg (s : Set ι)).mp hgout
  apply MonoidHom.ext
  intro x
  let tx : ∀ i, G i := fun i => if i ∈ s then x i else 1
  have hxt : ∀ i ∈ (s : Set ι), x i = tx i := by
    intro i hi
    have hi' : i ∈ s := hi
    change x i = if i ∈ s then x i else 1
    exact (ite_eq_left hi').symm
  calc
    f x = f tx := hdep_f x tx hxt
    _ = g tx := by
      apply map_coordinate_truncation_eq f g s x
      intro i hi
      calc
        f (Pi.mulSingle i (x i)) = f.coordinateHom i (x i) :=
          (coordinateHom_apply f i (x i)).symm
        _ = g.coordinateHom i (x i) :=
          congrArg (fun c : G i →* D => c (x i)) (heq i)
        _ = g (Pi.mulSingle i (x i)) := coordinateHom_apply g i (x i)
    _ = g x := (hdep_g x tx hxt).symm

end

end MonoidHom

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, MulOneClass (G i)] [MulOneClass D]

/-- The coordinates at which the coefficient homomorphism is nontrivial. -/
def coordinateMulSupport (f : (∀ i, G i) →* D) : Set ι :=
  {i | f.coordinateHom i ≠ 1}

@[simp]
theorem mem_coordinateMulSupport (f : (∀ i, G i) →* D) (i : ι) :
    i ∈ f.coordinateMulSupport ↔ f.coordinateHom i ≠ 1 :=
  Iff.rfl

theorem not_mem_coordinateMulSupport (f : (∀ i, G i) →* D) (i : ι) :
    i ∉ f.coordinateMulSupport ↔ f.coordinateHom i = 1 := by
  classical
  simp only [mem_coordinateMulSupport, not_not]

/-- Equality of coefficient homomorphisms preserves coordinate support. -/
theorem coordinateMulSupport_congr {f g : (∀ i, G i) →* D}
    (h : ∀ i, f.coordinateHom i = g.coordinateHom i) :
    f.coordinateMulSupport = g.coordinateMulSupport := by
  apply Set.ext
  intro i
  simp only [mem_coordinateMulSupport, h i]

/-- Coordinate support lies in `S` exactly when every coefficient homomorphism outside
`S` is trivial. -/
theorem coordinateMulSupport_subset_iff (f : (∀ i, G i) →* D) (S : Set ι) :
    f.coordinateMulSupport ⊆ S ↔ ∀ i, i ∉ S → f.coordinateHom i = 1 := by
  classical
  constructor
  · intro h i hi
    exact (not_mem_coordinateMulSupport f i).1 (fun hmem => hi (h hmem))
  · intro h i hi
    by_contra hnot
    exact (mem_coordinateMulSupport f i).1 hi (h i hnot)

end MonoidHom

/-- If `f` is one on vectors whose `S`-coordinates are one, then its values on
single-coordinate insertions outside `S` are one. -/
theorem Function.apply_mulSingle_eq_one_of_eq_one_on_tail
    {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, One (G i)] [One D] [DecidableEq ι]
    (f : (∀ i, G i) → D) (S : Set ι)
    (ht : ∀ x : ∀ i, G i, (∀ j ∈ S, x j = 1) → f x = 1)
    {i : ι} (hi : i ∉ S) (a : G i) :
    f (Pi.mulSingle i a) = 1 := by
  apply ht
  intro j hj
  have hji : j ≠ i := fun hji => hi (hji ▸ hj)
  exact Pi.mulSingle_eq_of_ne hji a

/-- If `f` is one when the `S`-coordinates are one, its coordinate support lies in `S`. -/
theorem MonoidHom.coordinateMulSupport_subset_of_eq_one_on_tail
    {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, MulOneClass (G i)] [MulOneClass D]
    (f : (∀ i, G i) →* D) (S : Set ι)
    (ht : ∀ x : ∀ i, G i, (∀ j ∈ S, x j = 1) → f x = 1) :
    f.coordinateMulSupport ⊆ S := by
  classical
  intro i hi
  by_contra hnot
  obtain ⟨a, ha⟩ :=
    (MonoidHom.coordinateHom_ne_one_iff f i).1
      ((MonoidHom.mem_coordinateMulSupport f i).1 hi)
  exact ha (Function.apply_mulSingle_eq_one_of_eq_one_on_tail
    (f : (∀ j, G j) → D) S ht hnot a)

/-- Continuity at one and inversion continuity at one give finite coordinate support. -/
theorem MonoidHom.finite_coordinateMulSupport_of_continuousAt_inv
    {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, MulOneClass (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D] [NoSmallSubgroups D]
    (f : (∀ i, G i) →* D) (hf : ContinuousAt f 1)
    (hinv : ContinuousAt (fun d : D => d⁻¹) (1 : D)) :
    f.coordinateMulSupport.Finite := by
  obtain ⟨s, hs⟩ :=
    MonoidHom.exists_finset_eq_one_of_coordinates_eq_one_of_continuousAt_inv f hf hinv
  exact s.finite_toSet.subset
    (MonoidHom.coordinateMulSupport_subset_of_eq_one_on_tail f (s : Set ι) hs)

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, MulOneClass (G i)] [MulOneClass D]

/-- A coordinate belongs to the support exactly when some coefficient value is nontrivial. -/
theorem mem_coordinateMulSupport_iff (f : (∀ i, G i) →* D) (i : ι) :
    i ∈ f.coordinateMulSupport ↔ ∃ a : G i, f.coordinateHom i a ≠ 1 := by
  simpa only [coordinateHom_apply] using
    (mem_coordinateMulSupport f i).trans (coordinateHom_ne_one_iff f i)

/-- A coordinate is outside the support exactly when all its coefficient values are one. -/
theorem not_mem_coordinateMulSupport_iff (f : (∀ i, G i) →* D) (i : ι) :
    i ∉ f.coordinateMulSupport ↔ ∀ a : G i, f.coordinateHom i a = 1 := by
  classical
  simp only [mem_coordinateMulSupport_iff, not_exists, not_not]

/-- Coordinate support lies in `S` exactly when every coefficient value outside `S` is one. -/
theorem coordinateMulSupport_subset_iff_coordinate_values_eq_one
    (f : (∀ i, G i) →* D) (S : Set ι) :
    f.coordinateMulSupport ⊆ S ↔ ∀ i, i ∉ S → ∀ a : G i, f.coordinateHom i a = 1 := by
  classical
  constructor
  · intro h i hi
    exact (not_mem_coordinateMulSupport_iff f i).1 (fun hmem => hi (h hmem))
  · intro h i hi
    by_contra hnot
    obtain ⟨a, ha⟩ := (mem_coordinateMulSupport_iff f i).1 hi
    exact ha (h i hnot a)

section

variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- Coordinate support lies in `S` exactly when agreement of input tuples on `S`
forces equality of their images. Thus support is the least determining set, even when
infinite. Here determination concerns coordinates in `S`, not `Set.EqOn` of two maps. -/
theorem coordinateMulSupport_subset_iff_eqOn [T0Space D]
    (f : (∀ i, G i) →* D) (hf : Continuous f) (S : Set ι) :
    f.coordinateMulSupport ⊆ S ↔
      ∀ x y : (∀ i, G i), (∀ i ∈ S, x i = y i) → f x = f y :=
  (coordinateMulSupport_subset_iff_coordinate_values_eq_one f S).trans
    (coordinate_values_eq_one_off_iff f hf S)

end

end MonoidHom

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, MulOneClass (G i)] [MulOneClass D]
  [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- The coordinate support of a continuous homomorphism into a `T0` space is finite
exactly when its values are determined by finitely many coordinates. -/
theorem finite_coordinateMulSupport_iff_exists_finset [T0Space D]
    (f : (∀ i, G i) →* D) (hf : Continuous f) :
    f.coordinateMulSupport.Finite ↔
      ∃ s : Finset ι, ∀ x y : (∀ i, G i),
        (∀ i ∈ s, x i = y i) → f x = f y := by
  classical
  constructor
  · intro hfin
    refine ⟨hfin.toFinset, ?_⟩
    exact (coordinateMulSupport_subset_iff_eqOn f hf
      (hfin.toFinset : Set ι)).mp (by
        intro i hi
        exact hfin.mem_toFinset.mpr hi)
  · rintro ⟨s, hs⟩
    exact s.finite_toSet.subset
      ((coordinateMulSupport_subset_iff_eqOn f hf (s : Set ι)).mpr hs)

/-- Two continuous homomorphisms into a `T0` space with equal coordinate
homomorphisms agree when the first has finite coordinate support. -/
theorem ext_of_coordinateHom_eq_of_finite_coordinateMulSupport [T0Space D]
    (f g : (∀ i, G i) →* D) (hf : Continuous f) (hg : Continuous g)
    (hfin : f.coordinateMulSupport.Finite)
    (heq : ∀ i, f.coordinateHom i = g.coordinateHom i) : f = g := by
  classical
  refine ext_of_coordinateHom_eq_of_eq_one_off_finset f g hf hg hfin.toFinset ?_ heq
  intro i hi
  exact (not_mem_coordinateMulSupport_iff f i).mp
    (fun hmem => hi (hfin.mem_toFinset.mpr hmem))

end MonoidHom

namespace MonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, MulOneClass (G i)] [MulOneClass D]

/-- Every set of coordinates through which a homomorphism factors contains its
coordinate support; the factor may be an arbitrary function. -/
theorem coordinateMulSupport_subset_of_eq_comp_restrict
    (f : (∀ i, G i) →* D) (S : Set ι) (g : (∀ i : S, G i) → D)
    (h : (f : (∀ i, G i) → D) =
      g ∘ (fun (x : ∀ i, G i) (i : S) => x i)) :
    f.coordinateMulSupport ⊆ S := by
  apply coordinateMulSupport_subset_of_eq_one_on_tail f S
  intro x hx
  have hx1 : (fun i : S => x i) = (fun i : S => (1 : G i)) := by
    funext i
    exact hx i i.property
  calc
    f x = g (fun i : S => x i) := congrFun h x
    _ = g (fun i : S => (1 : G i)) := congrArg g hx1
    _ = f 1 := (congrFun h 1).symm
    _ = 1 := f.map_one

end MonoidHom

namespace MonoidHom

section

variable {ι : Type u} {G : ι → Type v} {D : Type w}
variable [∀ i, MulOneClass (G i)] [MulOneClass D]
variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D] [T0Space D]

/-- A continuous homomorphism whose coefficient values outside `s` are trivial is the
composition of its finite-coordinate factor with restriction to `s`. -/
theorem eq_finiteCoordinateFactor_comp_restrict_of_coordinate_values_eq_one
    (f : (∀ i, G i) →* D) (hf : Continuous f) (s : Finset ι)
    (hc : ∀ i, i ∉ s → ∀ a : G i, f.coordinateHom i a = 1) :
    (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  classical
  have hdep : ∀ x y : (∀ i, G i),
      (∀ i ∈ (s : Set ι), x i = y i) → f x = f y :=
    (coordinate_values_eq_one_off_iff f hf (s : Set ι)).mp hc
  have hs : ∀ z : ∀ i, G i, (∀ i ∈ s, z i = 1) → f z = 1 := by
    intro z hz
    calc
      f z = f 1 := hdep z 1 (by
        intro i hi
        simpa only [Pi.one_apply] using hz i hi)
      _ = 1 := f.map_one
  exact eq_finiteCoordinateFactor_comp_restrict_of_eq_one f s hs

/-- The finite-coordinate factor evaluated on a restricted tuple recovers the original
value when every coefficient value outside `s` is trivial. -/
theorem finiteCoordinateFactor_restrict_of_coordinate_values_eq_one
    (f : (∀ i, G i) →* D) (hf : Continuous f) (s : Finset ι)
    (hc : ∀ i, i ∉ s → ∀ a : G i, f.coordinateHom i a = 1)
    (x : ∀ i, G i) :
    f.finiteCoordinateFactor s (fun i => x i) = f x := by
  exact (congrFun
    (eq_finiteCoordinateFactor_comp_restrict_of_coordinate_values_eq_one f hf s hc) x).symm

/-- For a continuous homomorphism into a `T0` space, a finite set contains the
coordinate support exactly when the canonical factor reconstructs the homomorphism. -/
theorem coordinateMulSupport_subset_iff_eq_finiteCoordinateFactor_comp_restrict
    (f : (∀ i, G i) →* D) (hf : Continuous f) (s : Finset ι) :
    f.coordinateMulSupport ⊆ (s : Set ι) ↔
      (f : (∀ i, G i) → D) =
        (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
          (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  constructor
  · intro hs
    exact eq_finiteCoordinateFactor_comp_restrict_of_coordinate_values_eq_one f hf s
      ((coordinateMulSupport_subset_iff_coordinate_values_eq_one f (s : Set ι)).mp hs)
  · intro h
    exact coordinateMulSupport_subset_of_eq_comp_restrict f (s : Set ι)
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) h

end

end MonoidHom
