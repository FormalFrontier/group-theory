/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Assembly of commuting coordinate homomorphisms

A finitely supported family of continuous monoid homomorphisms with
pairwise commuting distinct-coordinate ranges defines a continuous monoid
homomorphism on the dependent product. The source operations need not be
continuous, and the target need not be commutative.

## References

The finite noncommutative product API is due to Yakov Pechersky.
The dependent-product APIs are due to Simon Hudon, Patrick Massot and
Eric Wieser.
-/

@[expose] public section

universe u v w

namespace ContinuousMonoidHom

variable {ι : Type u} {Gi : ι → Type v} {D : Type w}
variable [∀ i, Monoid (Gi i)] [∀ i, TopologicalSpace (Gi i)]
variable [Monoid D] [TopologicalSpace D]
variable (c : DFinsupp (fun i => Additive (Gi i →ₜ* D)))
variable (hc : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
  Commute ((c i).toMul x) ((c j).toMul y))

include hc in
private theorem coordinateProduct_pairwise (S : Finset ι) (x : ∀ i, Gi i) :
    (S : Set ι).Pairwise
      (Function.onFun Commute (fun i => (c i).toMul (x i))) := by
  intro i _hi j _hj hij
  exact hc i j hij (x i) (x j)

private noncomputable def coordinateProduct (S : Finset ι) (x : ∀ i, Gi i) : D :=
  S.noncommProd (fun i => (c i).toMul (x i))
    (coordinateProduct_pairwise c hc S x)

private theorem coordinateProduct_empty (x : ∀ i, Gi i) :
    coordinateProduct c hc ∅ x = 1 := by
  exact Finset.noncommProd_empty (fun i => (c i).toMul (x i))
    (coordinateProduct_pairwise c hc ∅ x)

private theorem coordinateProduct_cons (S : Finset ι) (a : ι)
    (ha : a ∉ S) (x : ∀ i, Gi i) :
    coordinateProduct c hc (Finset.cons a S ha) x =
      (c a).toMul (x a) * coordinateProduct c hc S x := by
  exact Finset.noncommProd_cons S a (fun i => (c i).toMul (x i)) ha
    (coordinateProduct_pairwise c hc (Finset.cons a S ha) x)

private theorem coordinateProduct_insert [DecidableEq ι]
    (S : Finset ι) (a : ι) (ha : a ∉ S) (x : ∀ i, Gi i) :
    coordinateProduct c hc (insert a S) x =
      (c a).toMul (x a) * coordinateProduct c hc S x := by
  exact Finset.noncommProd_insert_of_notMem S a
    (fun i => (c i).toMul (x i))
    (coordinateProduct_pairwise c hc (insert a S) x) ha

private theorem coordinateProduct_singleton (k : ι) (x : ∀ i, Gi i) :
    coordinateProduct c hc {k} x = (c k).toMul (x k) := by
  have hset : Finset.cons k ∅ (Finset.notMem_empty k) = {k} := by
    classical
    ext j
    simp
  calc
    coordinateProduct c hc {k} x =
        coordinateProduct c hc (Finset.cons k ∅ (Finset.notMem_empty k)) x :=
      congrArg (fun T => coordinateProduct c hc T x) hset.symm
    _ = (c k).toMul (x k) * coordinateProduct c hc ∅ x :=
      coordinateProduct_cons c hc ∅ k (Finset.notMem_empty k) x
    _ = (c k).toMul (x k) := by rw [coordinateProduct_empty, mul_one]

private theorem zero_coefficient_apply (i : ι) (hi : c i = 0)
    (a : Gi i) : (c i).toMul a = 1 := by
  rw [hi, toMul_zero]
  simpa only [Pi.one_apply] using
    congrFun (coe_one (Gi i) D : ⇑(1 : Gi i →ₜ* D) = 1) a

private theorem coordinateProduct_one (S : Finset ι) :
    coordinateProduct c hc S 1 = 1 := by
  exact Finset.noncommProd_induction S (fun i => (c i).toMul ((1 : ∀ i, Gi i) i))
    (coordinateProduct_pairwise c hc S 1) (fun z => z = 1)
    (fun a b ha hb => by rw [ha, hb, mul_one]) rfl
    (fun i _hi => by
      simpa only [Pi.one_apply] using map_one ((c i).toMul))

private theorem coordinateProduct_mul (S : Finset ι)
    (x y : ∀ i, Gi i) :
    coordinateProduct c hc S (x * y) =
      coordinateProduct c hc S x * coordinateProduct c hc S y := by
  have hfun :
      (fun i => (c i).toMul ((x * y) i)) =
        (fun i => (c i).toMul (x i)) * (fun i => (c i).toMul (y i)) := by
    funext i
    simp only [Pi.mul_apply, map_mul]
  have hcross : (S : Set ι).Pairwise
      (fun i j => Commute ((c i).toMul (y i)) ((c j).toMul (x j))) := by
    intro i _hi j _hj hij
    exact hc i j hij (y i) (x j)
  simpa only [coordinateProduct, hfun] using
    (Finset.noncommProd_mul_distrib (s := S)
      (fun i => (c i).toMul (x i)) (fun i => (c i).toMul (y i))
      (coordinateProduct_pairwise c hc S x)
      (coordinateProduct_pairwise c hc S y) hcross)

variable [ContinuousMul D]

private theorem continuous_coordinateProduct (S : Finset ι) :
    Continuous (coordinateProduct c hc S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hzero : coordinateProduct c hc ∅ =
          fun _ : (∀ i, Gi i) => (1 : D) := by
        funext x
        exact coordinateProduct_empty c hc x
      rw [hzero]
      exact continuous_const
  | @insert a S ha ih =>
      have hstep : coordinateProduct c hc (insert a S) =
          fun x => (c a).toMul (x a) * coordinateProduct c hc S x := by
        funext x
        exact coordinateProduct_insert c hc S a ha x
      rw [hstep]
      exact (((c a).toMul).continuous_toFun.comp (continuous_apply a)).mul ih

omit [ContinuousMul D] in
private theorem coordinateProduct_eq_of_agree (S : Finset ι)
    (x y : ∀ i, Gi i) :
    (∀ i ∈ S, x i = y i) →
      coordinateProduct c hc S x = coordinateProduct c hc S y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _hxy
      exact (coordinateProduct_empty c hc x).trans
        (coordinateProduct_empty c hc y).symm
  | @insert a S ha ih =>
      intro hxy
      have hstep (z : ∀ i, Gi i) :
          coordinateProduct c hc (insert a S) z =
            (c a).toMul (z a) * coordinateProduct c hc S z :=
        coordinateProduct_insert c hc S a ha z
      rw [hstep x, hstep y, hxy a (Finset.mem_insert_self a S),
        ih (fun i hi => hxy i (Finset.mem_insert_of_mem hi))]

/-- Assemble a finitely supported family whose distinct-coordinate ranges
commute. The underlying function is the product over the coefficient support. -/
noncomputable def ofDFinsupp : (∀ i, Gi i) →ₜ* D := by
  classical
  exact
    { toFun := fun x =>
        Finset.noncommProd c.support (fun i => (c i).toMul (x i))
          (fun i _hi j _hj hij => hc i j hij (x i) (x j))
      map_one' := by exact coordinateProduct_one c hc c.support
      map_mul' := by exact coordinateProduct_mul c hc c.support
      continuous_toFun := by exact continuous_coordinateProduct c hc c.support }

omit [ContinuousMul D] in
/-- Enlarging a finite cover of the nonzero coefficients leaves the product
unchanged. -/
theorem ofDFinsupp_noncommProd_mono
    (S T : Finset ι) (hST : S ⊆ T)
    (hS : ∀ i, c i ≠ 0 → i ∈ S) (x : ∀ i, Gi i) :
    S.noncommProd (fun i => (c i).toMul (x i))
      (fun i _hi j _hj hij => hc i j hij (x i) (x j)) =
    T.noncommProd (fun i => (c i).toMul (x i))
      (fun i _hi j _hj hij => hc i j hij (x i) (x j)) := by
  classical
  change coordinateProduct c hc S x = coordinateProduct c hc T x
  have hrest : coordinateProduct c hc (T \ S) x = 1 := by
    refine Finset.noncommProd_induction (T \ S)
      (fun i => (c i).toMul (x i))
      (coordinateProduct_pairwise c hc (T \ S) x) (fun z => z = 1)
      (fun a b ha hb => by rw [ha, hb, mul_one]) rfl ?_
    intro i hi
    apply zero_coefficient_apply c i
    by_contra hci
    exact (Finset.mem_sdiff.mp hi).2 (hS i hci)
  have hd : Disjoint S (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiD
    exact (Finset.mem_sdiff.mp hiD).2 hiS
  have hu : S ∪ (T \ S) = T := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hiS | hiD
      · exact hST hiS
      · exact (Finset.mem_sdiff.mp hiD).1
    · intro hi
      by_cases hiS : i ∈ S
      · exact Finset.mem_union.mpr (Or.inl hiS)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hi, hiS⟩))
  have hp : coordinateProduct c hc (S ∪ (T \ S)) x =
      coordinateProduct c hc S x * coordinateProduct c hc (T \ S) x := by
    exact Finset.noncommProd_union_of_disjoint hd
      (fun i => (c i).toMul (x i))
      (coordinateProduct_pairwise c hc (S ∪ (T \ S)) x)
  rw [hu, hrest, mul_one] at hp
  exact hp.symm

/-- Evaluate the assembled homomorphism over any finite cover of the nonzero
coefficients. -/
theorem ofDFinsupp_apply
    (S : Finset ι) (hS : ∀ i, c i ≠ 0 → i ∈ S)
    (x : ∀ i, Gi i) :
    ofDFinsupp c hc x =
      S.noncommProd (fun i => (c i).toMul (x i))
        (fun i _hi j _hj hij => hc i j hij (x i) (x j)) := by
  classical
  change coordinateProduct c hc c.support x = coordinateProduct c hc S x
  exact ofDFinsupp_noncommProd_mono c hc c.support S
    (fun i hi => hS i (DFinsupp.mem_support_iff.mp hi))
    (fun i hi => DFinsupp.mem_support_iff.mpr hi) x

/-- The assembled homomorphism depends only on a finite cover of its
nonzero coefficients. -/
theorem ofDFinsupp_apply_eq_of_agree
    (S : Finset ι) (hS : ∀ i, c i ≠ 0 → i ∈ S)
    (x y : ∀ i, Gi i) (hxy : ∀ i ∈ S, x i = y i) :
    ofDFinsupp c hc x = ofDFinsupp c hc y := by
  calc
    ofDFinsupp c hc x = coordinateProduct c hc S x :=
      ofDFinsupp_apply c hc S hS x
    _ = coordinateProduct c hc S y := coordinateProduct_eq_of_agree c hc S x y hxy
    _ = ofDFinsupp c hc y := (ofDFinsupp_apply c hc S hS y).symm

/-- If only one coordinate can have a nonzero coefficient, assembly is
the corresponding coordinate homomorphism after projection. -/
theorem ofDFinsupp_apply_of_support_singleton
    (k : ι) (hk : ∀ i, c i ≠ 0 → i = k) (x : ∀ i, Gi i) :
    ofDFinsupp c hc x = (c k).toMul (x k) := by
  have hcover : ∀ i, c i ≠ 0 → i ∈ ({k} : Finset ι) :=
    fun i hi => Finset.mem_singleton.mpr (hk i hi)
  exact (ofDFinsupp_apply c hc {k} hcover x).trans
    (coordinateProduct_singleton c hc k x)

/-- Evaluation at a single-coordinate insertion recovers the corresponding coefficient. -/
theorem ofDFinsupp_mulSingle [DecidableEq ι] (i : ι) (a : Gi i) :
    ofDFinsupp c hc (Pi.mulSingle i a) = (c i).toMul a := by
  let _ : ∀ (j : ι) (z : Additive (Gi j →ₜ* D)), Decidable (z ≠ 0) :=
    fun _ _ => Classical.propDecidable _
  let S : Finset ι := c.support.erase i
  have hcover : ∀ j, c j ≠ 0 → j ∈ insert i S := by
    intro j hj
    by_cases hji : j = i
    · subst j
      exact Finset.mem_insert_self i S
    · have hmem : j ∈ c.support := DFinsupp.mem_support_iff.mpr hj
      apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨hji, hmem⟩
  have hiS : i ∉ S := by
    exact Finset.notMem_erase i c.support
  have hrest : coordinateProduct c hc S (Pi.mulSingle i a) = 1 := by
    refine Finset.noncommProd_induction S
      (fun j => (c j).toMul (Pi.mulSingle i a j))
      (coordinateProduct_pairwise c hc S (Pi.mulSingle i a)) (fun z => z = 1)
      (fun b d hb hd => by rw [hb, hd, mul_one]) rfl ?_
    intro j hj
    have hji : j ≠ i := by
      intro h
      subst j
      exact hiS hj
    rw [Pi.mulSingle_eq_of_ne hji]
    exact map_one ((c j).toMul)
  calc
    ofDFinsupp c hc (Pi.mulSingle i a) =
        coordinateProduct c hc (insert i S) (Pi.mulSingle i a) :=
      ofDFinsupp_apply c hc (insert i S) hcover (Pi.mulSingle i a)
    _ = (c i).toMul (Pi.mulSingle i a i) *
        coordinateProduct c hc S (Pi.mulSingle i a) :=
      coordinateProduct_insert c hc S i hiS (Pi.mulSingle i a)
    _ = (c i).toMul a := by rw [Pi.mulSingle_eq_same, hrest, mul_one]

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {Gi : ι → Type v} {D : Type w}
variable [∀ i, Monoid (Gi i)] [∀ i, TopologicalSpace (Gi i)]
variable [Monoid D] [TopologicalSpace D] [ContinuousMul D]

section Equality

variable
  (c : DFinsupp (fun i => Additive (Gi i →ₜ* D)))
  (hc : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
    Commute ((c i).toMul x) ((c j).toMul y))

/-- Assembly detects equality of compatible finitely supported families. -/
theorem ofDFinsupp_eq_iff
    (d : DFinsupp (fun i => Additive (Gi i →ₜ* D)))
    (hd : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
      Commute ((d i).toMul x) ((d j).toMul y)) :
    ofDFinsupp c hc = ofDFinsupp d hd ↔ c = d := by
  classical
  constructor
  · intro h
    apply DFinsupp.ext
    intro i
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro a
    simpa only [ofDFinsupp_mulSingle] using
      congrArg (fun f : (∀ j, Gi j) →ₜ* D =>
        f (Pi.mulSingle i a)) h
  · intro h
    subst d
    rfl

end Equality

/-- The zero coefficient family assembles to the trivial homomorphism. -/
theorem ofDFinsupp_zero
    (hc0 : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
      Commute
        (((0 : DFinsupp (fun k => Additive (Gi k →ₜ* D))) i).toMul x)
        (((0 : DFinsupp (fun k => Additive (Gi k →ₜ* D))) j).toMul y)) :
    ofDFinsupp (0 : DFinsupp (fun i => Additive (Gi i →ₜ* D))) hc0 = 1 := by
  apply ContinuousMonoidHom.ext
  intro x
  have hcover :
      ∀ i, (0 : DFinsupp (fun k => Additive (Gi k →ₜ* D))) i ≠ 0 →
        i ∈ (∅ : Finset ι) := by
    intro i hi
    exact (hi (DFinsupp.zero_apply i)).elim
  exact (ofDFinsupp_apply
    (0 : DFinsupp (fun i => Additive (Gi i →ₜ* D))) hc0 ∅ hcover x).trans
      ((coordinateProduct_empty
        (0 : DFinsupp (fun i => Additive (Gi i →ₜ* D))) hc0 x).trans
        (by
          simpa only [Pi.one_apply] using
            (congrFun (ContinuousMonoidHom.coe_one
              (A := ∀ i, Gi i) (B := D)) x).symm))

section ZeroCharacterization

variable
  (c : DFinsupp (fun i => Additive (Gi i →ₜ* D)))
  (hc : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
    Commute ((c i).toMul x) ((c j).toMul y))

/-- Assembly is trivial exactly for the zero coefficient family. -/
theorem ofDFinsupp_eq_one_iff :
    ofDFinsupp c hc = 1 ↔ c = 0 := by
  have hc0 :
      ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
        Commute
          (((0 : DFinsupp (fun k => Additive (Gi k →ₜ* D))) i).toMul x)
          (((0 : DFinsupp (fun k => Additive (Gi k →ₜ* D))) j).toMul y) := by
    intro i j _ x y
    simpa only [DFinsupp.zero_apply, toMul_zero,
      ContinuousMonoidHom.coe_one, Pi.one_apply] using
      (show Commute (1 : D) 1 from rfl)
  constructor
  · intro h
    exact (ofDFinsupp_eq_iff c hc 0 hc0).mp
      (h.trans (ofDFinsupp_zero hc0).symm)
  · intro h
    exact ((ofDFinsupp_eq_iff c hc 0 hc0).mpr h).trans
      (ofDFinsupp_zero hc0)

end ZeroCharacterization

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {Gi : ι → Type v} {D : Type w}
variable [∀ i, Monoid (Gi i)] [∀ i, TopologicalSpace (Gi i)]
variable [Monoid D] [TopologicalSpace D] [ContinuousMul D]
variable
  (c : DFinsupp (fun i => Additive (Gi i →ₜ* D)))
  (hc : ∀ (i j : ι), i ≠ j → ∀ (x : Gi i) (y : Gi j),
    Commute ((c i).toMul x) ((c j).toMul y))

private theorem ofDFinsupp_apply_eq_of_trivial_off
    (f : (∀ i, Gi i) →ₜ* D) (S : Finset ι) :
    (∀ i ∈ S, ∀ (z : ∀ j, Gi j),
      (∀ j, j ≠ i → z j = 1) → f z = (c i).toMul (z i)) →
    ∀ (z : ∀ i, Gi i), (∀ i, i ∉ S → z i = 1) →
      f z = ofDFinsupp c hc z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ z hz
    have hz1 : z = 1 := by
      funext i
      simpa only [Pi.one_apply] using hz i (by simp)
    simp only [hz1, map_one]
  | @insert i S _ ih =>
    intro hcoord z hz
    -- Remove the selected coordinate, leaving an original tuple on the smaller set.
    let y : ∀ j, Gi j := fun j => if j = i then 1 else z j
    have hy : ∀ j, j ∉ S → y j = 1 := by
      intro j hj
      by_cases hji : j = i
      · simp only [y, ite_eq_left hji]
      · simp only [y, ite_eq_right hji]
        apply hz j
        intro hj'
        rcases Finset.mem_insert.mp hj' with hji' | hj'
        · exact hji hji'
        · exact hj hj'
    have hsplit : z = Pi.mulSingle i (z i) * y := by
      funext j
      rw [Pi.mul_apply]
      change z j = Pi.mulSingle i (z i) j *
        (if j = i then 1 else z j)
      by_cases hji : j = i
      · subst j
        rw [Pi.mulSingle_eq_same, ite_eq_left rfl, mul_one]
      · rw [Pi.mulSingle_eq_of_ne hji (z i), ite_eq_right hji, one_mul]
    have hsingle : ∀ j, j ≠ i → Pi.mulSingle i (z i) j = 1 :=
      fun j hj => Pi.mulSingle_eq_of_ne hj (z i)
    have hfi : f (Pi.mulSingle i (z i)) = (c i).toMul (z i) := by
      simpa only [Pi.mulSingle_eq_same] using
        hcoord i (Finset.mem_insert_self i S)
          (Pi.mulSingle i (z i)) hsingle
    have hfy : f y = ofDFinsupp c hc y :=
      ih (fun j hj => hcoord j (Finset.mem_insert_of_mem hj)) y hy
    calc
      f z = f (Pi.mulSingle i (z i) * y) := congrArg f hsplit
      _ = f (Pi.mulSingle i (z i)) * f y := map_mul f _ _
      _ = (c i).toMul (z i) * ofDFinsupp c hc y := by rw [hfi, hfy]
      _ = ofDFinsupp c hc (Pi.mulSingle i (z i)) *
          ofDFinsupp c hc y := by rw [ofDFinsupp_mulSingle]
      _ = ofDFinsupp c hc (Pi.mulSingle i (z i) * y) :=
        (map_mul (ofDFinsupp c hc) _ _).symm
      _ = ofDFinsupp c hc z := congrArg (ofDFinsupp c hc) hsplit.symm

/-- On a finite index type, agreement on tuples trivial off a single coordinate
identifies the assembled continuous monoid homomorphism. -/
theorem ofDFinsupp_unique_of_finite
    [Finite ι] (f : (∀ i, Gi i) →ₜ* D)
    (hcoord : ∀ (i : ι) (z : ∀ j, Gi j),
      (∀ j, j ≠ i → z j = 1) → f z = (c i).toMul (z i)) :
    f = ofDFinsupp c hc := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  apply ContinuousMonoidHom.ext
  intro x
  exact ofDFinsupp_apply_eq_of_trivial_off c hc f Finset.univ
    (fun i _ => hcoord i) x (by
      intro i hi
      exact False.elim (hi (Finset.mem_univ i)))

/-- Finite dependence and agreement on tuples trivial off a single coordinate
identify the assembly from any finite cover of the coefficient family. -/
theorem ofDFinsupp_unique_of_dependsOn
    (S : Finset ι) (hS : ∀ i, c i ≠ 0 → i ∈ S)
    (f : (∀ i, Gi i) →ₜ* D)
    (hdepend : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hcoord : ∀ i ∈ S, ∀ (z : ∀ j, Gi j),
      (∀ j, j ≠ i → z j = 1) → f z = (c i).toMul (z i)) :
    f = ofDFinsupp c hc := by
  classical
  apply ContinuousMonoidHom.ext
  intro x
  let y : ∀ i, Gi i := fun i => if i ∈ S then x i else 1
  have hxy : ∀ i ∈ S, x i = y i := by
    intro i hi
    simp only [y, ite_eq_left hi]
  have hy : ∀ i, i ∉ S → y i = 1 := by
    intro i hi
    simp only [y, ite_eq_right hi]
  calc
    f x = f y := hdepend x y hxy
    _ = ofDFinsupp c hc y :=
      ofDFinsupp_apply_eq_of_trivial_off c hc f S hcoord y hy
    _ = ofDFinsupp c hc x :=
      ofDFinsupp_apply_eq_of_agree c hc S hS y x
        (fun i hi => (hxy i hi).symm)

end ContinuousMonoidHom
