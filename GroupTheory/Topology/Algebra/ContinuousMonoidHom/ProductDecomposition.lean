/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.CoordinateAssembly
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Coordinates
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import Mathlib.Data.DFinsupp.BigOperators

/-!
# Finite-support decomposition of continuous product homomorphisms

For a product of groups and a commutative group with continuous multiplication and
no small subgroups, restriction to the individual coordinates identifies continuous
homomorphisms with finitely supported families of continuous homomorphisms. This is
a commutative-monoid equivalence: continuity of inversion is not assumed.

The inverse construction `ContinuousMonoidHom.dfinsuppProd` needs only monoids in
the source and a commutative monoid with continuous multiplication in the target.
It specializes `ContinuousMonoidHom.ofDFinsupp` to a commutative target and
bundles multiplication of the coefficient families. Its value is the finite
product of the coordinate evaluations.

Finiteness of the entire family of nontrivial coefficient maps follows from the
finite-coordinate-kernel theorem. Reconstruction uses finite induction on the
coordinates in the source and a finite product only in the commutative target;
the source groups need not commute. All topologies are the given topologies, with
the product topology on the source. No continuity of source operations is needed.
-/

@[expose] public section

open scoped BigOperators

universe u v w

variable {ι : Type u} {G : ι → Type v} {D : Type w}

attribute [local instance] Classical.propDecidable

namespace ContinuousMonoidHom

section MulOneClass

variable [∀ i, MulOneClass (G i)]

private theorem map_coordinate_truncation [CommMonoid D] (f : (∀ i, G i) →* D)
    (s : Finset ι) (x : ∀ i, G i) :
    f (fun i => if i ∈ s then x i else 1) =
      ∏ i ∈ s, f (Pi.mulSingle i (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have he : (fun i => if i ∈ (∅ : Finset ι) then x i else 1) = (1 : ∀ i, G i) := by
        funext i
        simp
      rw [he, Finset.prod_empty]
      exact map_one f
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ← ih, ← map_mul]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp [hi]
      · simp [hji]

end MulOneClass

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

end Monoid

section CommMonoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [CommMonoid D] [TopologicalSpace D] [ContinuousMul D]

@[simp]
theorem coordinateHom_mul (f g : (∀ i, G i) →ₜ* D) (i : ι) :
    (f * g).coordinateHom i = f.coordinateHom i * g.coordinateHom i := by
  apply DFunLike.ext
  intro t
  rfl

/-- Assemble a finitely supported family of continuous coordinate homomorphisms.
This bundles the commutative specialization of `ofDFinsupp` as a monoid homomorphism
on coefficient families. -/
noncomputable def dfinsuppProd :
    Multiplicative (Π₀ i, Additive (G i →ₜ* D)) →* ((∀ i, G i) →ₜ* D) := by
  refine
    { toFun := fun a => ofDFinsupp a.toAdd (fun _ _ _ _ _ => mul_comm _ _)
      map_one' := ofDFinsupp_zero (Gi := G) (D := D) (fun _ _ _ _ _ => mul_comm _ _)
      map_mul' := ?_ }
  intro a b
  classical
  let s : Finset ι := a.toAdd.support ∪ b.toAdd.support
  have ha : ∀ i, a.toAdd i ≠ 0 → i ∈ s := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inl (DFinsupp.mem_support_iff.mpr hi))
  have hb : ∀ i, b.toAdd i ≠ 0 → i ∈ s := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inr (DFinsupp.mem_support_iff.mpr hi))
  have hab : ∀ i, (a * b).toAdd i ≠ 0 → i ∈ s := by
    intro i hi
    by_contra his
    have hai : a.toAdd i = 0 := by
      by_contra hn
      exact his (ha i hn)
    have hbi : b.toAdd i = 0 := by
      by_contra hn
      exact his (hb i hn)
    apply hi
    change a.toAdd i + b.toAdd i = 0
    rw [hai, hbi, add_zero]
  apply DFunLike.ext
  intro x
  change ofDFinsupp (a * b).toAdd (fun _ _ _ _ _ => mul_comm _ _) x =
    ofDFinsupp a.toAdd (fun _ _ _ _ _ => mul_comm _ _) x *
      ofDFinsupp b.toAdd (fun _ _ _ _ _ => mul_comm _ _) x
  rw [ofDFinsupp_apply_eq_prod (a * b).toAdd
      (fun _ _ _ _ _ => mul_comm _ _) s hab x,
    ofDFinsupp_apply_eq_prod a.toAdd (fun _ _ _ _ _ => mul_comm _ _) s ha x,
    ofDFinsupp_apply_eq_prod b.toAdd (fun _ _ _ _ _ => mul_comm _ _) s hb x,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change ((a.toAdd i).toMul * (b.toAdd i).toMul) (x i) =
    (a.toAdd i).toMul (x i) * (b.toAdd i).toMul (x i)
  rfl

/-- Evaluation of the assembled homomorphism is the product over the coefficient
support. The product is taken in the commutative target, not in the source. -/
theorem dfinsuppProd_apply
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) (x : ∀ i, G i) :
    dfinsuppProd a x = ∏ i ∈ a.toAdd.support, (a.toAdd i).toMul (x i) := by
  exact ofDFinsupp_apply_eq_prod a.toAdd (fun _ _ _ _ _ => mul_comm _ _)
    a.toAdd.support (fun i hi => DFinsupp.mem_support_iff.mpr hi) x

/-- Any finite superset of the coefficient support gives the same product. -/
theorem dfinsuppProd_apply_of_support_subset
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) (s : Finset ι)
    (hs : a.toAdd.support ⊆ s) (x : ∀ i, G i) :
    dfinsuppProd a x = ∏ i ∈ s, (a.toAdd i).toMul (x i) := by
  classical
  rw [dfinsuppProd_apply]
  apply Finset.prod_subset hs
  intro i _ hi
  have hai : a.toAdd i = 0 := by simpa using hi
  simp [hai]

@[simp]
theorem dfinsuppProd_one :
    dfinsuppProd (G := G) (D := D) 1 = 1 := map_one _

@[simp]
theorem dfinsuppProd_mul
    (a b : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) :
    dfinsuppProd (a * b) = dfinsuppProd a * dfinsuppProd b := map_mul _ _ _

@[simp]
theorem dfinsuppProd_single_apply (i : ι) (g : G i →ₜ* D) (x : ∀ i, G i) :
    dfinsuppProd (Multiplicative.ofAdd (DFinsupp.single i (Additive.ofMul g))) x =
      g (x i) := by
  classical
  let c : Π₀ j, Additive (G j →ₜ* D) := DFinsupp.single i (Additive.ofMul g)
  have hsupport : ∀ j, c j ≠ 0 → j = i := by
    intro j hj
    by_contra hji
    exact hj (by simp [c, Ne.symm hji])
  calc
    dfinsuppProd (Multiplicative.ofAdd (DFinsupp.single i (Additive.ofMul g))) x =
        (c i).toMul (x i) :=
      ofDFinsupp_apply_of_support_singleton c (fun _ _ _ _ _ => mul_comm _ _) i hsupport x
    _ = g (x i) := by simp [c]

/-- The restrictions of the assembled homomorphism are exactly its coefficients. -/
@[simp]
theorem coordinateHom_dfinsuppProd
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) (i : ι) :
    (dfinsuppProd a).coordinateHom i = (a.toAdd i).toMul := by
  classical
  apply DFunLike.ext
  intro t
  rw [coordinateHom_apply]
  exact ofDFinsupp_mulSingle a.toAdd (fun _ _ _ _ _ => mul_comm _ _) i t

end CommMonoid

section Group

variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D]

/-- Killing a coordinate kernel makes every coefficient outside that set trivial. -/
theorem coordinateHom_eq_one_of_coordinateKernel_le_ker
    (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker)
    (i : ι) (hi : i ∉ s) : f.coordinateHom i = 1 := by
  classical
  apply DFunLike.ext
  intro t
  rw [coordinateHom_apply]
  apply MonoidHom.mem_ker.mp
  apply hs
  intro j hj
  apply Subgroup.mem_bot.mpr
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [hji]

variable [NoSmallSubgroups D]

/-- Only finitely many entire coordinate restrictions are nontrivial. -/
theorem finite_mulSupport_coordinateHom (f : (∀ i, G i) →ₜ* D) :
    ({i : ι | f.coordinateHom i ≠ 1} : Set ι).Finite := by
  obtain ⟨s, hs⟩ :=
    f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
  apply s.finite_toSet.subset
  intro i hi
  change f.coordinateHom i ≠ 1 at hi
  by_contra his
  exact hi (f.coordinateHom_eq_one_of_coordinateKernel_le_ker s hs i his)

/-- The finitely supported family of coordinate restrictions of a continuous
product homomorphism into a group with no small subgroups. -/
noncomputable def productCoefficients (f : (∀ i, G i) →ₜ* D) :
    Π₀ i, Additive (G i →ₜ* D) := by
  classical
  exact DFinsupp.mk f.finite_mulSupport_coordinateHom.toFinset
    (fun i => Additive.ofMul (f.coordinateHom i))

@[simp]
theorem productCoefficients_apply (f : (∀ i, G i) →ₜ* D) (i : ι) :
    f.productCoefficients i = Additive.ofMul (f.coordinateHom i) := by
  classical
  by_cases h : f.coordinateHom i = 1
  · simp [productCoefficients, DFinsupp.mk_apply, h]
  · have hi : i ∈ f.finite_mulSupport_coordinateHom.toFinset := by
      simpa using h
    simp only [productCoefficients, DFinsupp.mk_of_mem hi]

theorem mem_support_productCoefficients (f : (∀ i, G i) →ₜ* D) (i : ι) :
    i ∈ f.productCoefficients.support ↔ f.coordinateHom i ≠ 1 := by
  classical
  simp

@[simp]
theorem productCoefficients_one :
    (1 : (∀ i, G i) →ₜ* D).productCoefficients = 0 := by
  ext i
  simp

/-- Coordinate restrictions determine a continuous homomorphism into a group
with no small subgroups. -/
theorem ext_coordinateHom {f g : (∀ i, G i) →ₜ* D}
    (h : ∀ i, f.coordinateHom i = g.coordinateHom i) : f = g := by
  classical
  obtain ⟨s, hs⟩ :=
    f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
  obtain ⟨t, ht⟩ :=
    g.toMonoidHom.exists_finset_coordinateKernel_le_ker g.continuous.continuousAt
  have hsf : Subgroup.pi ((s ∪ t : Finset ι) : Set ι)
      (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker := by
    intro x hx
    apply hs
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inl hi))
  have htg : Subgroup.pi ((s ∪ t : Finset ι) : Set ι)
      (fun i => (⊥ : Subgroup (G i))) ≤ g.toMonoidHom.ker := by
    intro x hx
    apply ht
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inr hi))
  apply DFunLike.ext
  intro x
  calc
    f x = f (fun i => if i ∈ s ∪ t then x i else 1) := by
      simpa [finiteCoordinateFactor_apply] using
        (f.finiteCoordinateFactor_restrict (s ∪ t) hsf x).symm
    _ = g (fun i => if i ∈ s ∪ t then x i else 1) := by
      apply MonoidHom.map_coordinate_truncation_eq f.toMonoidHom g.toMonoidHom (s ∪ t) x
      intro i _
      change f (Pi.mulSingle i (x i)) = g (Pi.mulSingle i (x i))
      simpa only [coordinateHom_apply] using
        congrArg (fun k : G i →ₜ* D => k (x i)) (h i)
    _ = g x := by
      simpa [finiteCoordinateFactor_apply] using
        g.finiteCoordinateFactor_restrict (s ∪ t) htg x

/-- Equality of continuous product homomorphisms can be checked on all coordinate
insertions. -/
theorem ext_coordinateHom_iff (f g : (∀ i, G i) →ₜ* D) :
    f = g ↔ ∀ i, f.coordinateHom i = g.coordinateHom i := by
  constructor
  · rintro rfl i
    rfl
  · exact ext_coordinateHom

/-- Pointwise coordinate insertion is an extensionality criterion. -/
theorem ext_mulSingle {f g : (∀ i, G i) →ₜ* D}
    (h : ∀ i (t : G i), f (Pi.mulSingle i t) = g (Pi.mulSingle i t)) : f = g := by
  apply ext_coordinateHom
  intro i
  apply DFunLike.ext
  intro t
  simpa only [coordinateHom_apply] using h i t

/-- A finite set kills the whole off-set coordinate subgroup exactly when it
contains the support of the family of nontrivial coordinate restrictions. Thus
this support is the unique minimal finite determining set. -/
theorem coordinateKernel_le_ker_iff_support_subset
    (f : (∀ i, G i) →ₜ* D) (s : Finset ι) :
    Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker ↔
      f.productCoefficients.support ⊆ s := by
  classical
  constructor
  · intro hs i hi
    by_contra his
    exact (mem_support_productCoefficients f i).mp hi
      (f.coordinateHom_eq_one_of_coordinateKernel_le_ker s hs i his)
  · intro hs x hx
    apply MonoidHom.mem_ker.mpr
    obtain ⟨t, ht⟩ :=
      f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
    have hsingle : ∀ i, f (Pi.mulSingle i (x i)) = 1 := by
      intro i
      by_cases his : i ∈ s
      · have hxi : x i = 1 := Subgroup.mem_bot.mp (hx i his)
        simp [hxi]
      · have hfi : f.coordinateHom i = 1 := by
          by_contra hfi
          exact his (hs ((mem_support_productCoefficients f i).mpr hfi))
        simpa using congrArg (fun k : G i →ₜ* D => k (x i)) hfi
    calc
      f x = f (fun i => if i ∈ t then x i else 1) := by
        simpa [finiteCoordinateFactor_apply] using
          (f.finiteCoordinateFactor_restrict t ht x).symm
      _ = (1 : (∀ i, G i) →* D) (fun i => if i ∈ t then x i else 1) := by
        apply MonoidHom.map_coordinate_truncation_eq f.toMonoidHom 1 t x
        intro i _
        simpa using hsingle i
      _ = 1 := rfl

end Group

section CommGroup

variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [CommGroup D] [TopologicalSpace D] [ContinuousMul D] [NoSmallSubgroups D]

@[simp]
theorem productCoefficients_mul (f g : (∀ i, G i) →ₜ* D) :
    (f * g).productCoefficients = f.productCoefficients + g.productCoefficients := by
  ext i
  simp

/-- Reassembling the coordinate restrictions recovers the homomorphism on the
whole product, including elements with infinitely many nonidentity coordinates. -/
@[simp]
theorem dfinsuppProd_productCoefficients (f : (∀ i, G i) →ₜ* D) :
    dfinsuppProd (Multiplicative.ofAdd f.productCoefficients) = f := by
  classical
  obtain ⟨s, hs⟩ :=
    f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
  have hsupp : f.productCoefficients.support ⊆ s := by
    intro i hi
    by_contra his
    exact (mem_support_productCoefficients f i).mp hi
      (f.coordinateHom_eq_one_of_coordinateKernel_le_ker s hs i his)
  apply DFunLike.ext
  intro x
  calc
    dfinsuppProd (Multiplicative.ofAdd f.productCoefficients) x =
        ∏ i ∈ s, (f.productCoefficients i).toMul (x i) :=
      dfinsuppProd_apply_of_support_subset _ s hsupp x
    _ = ∏ i ∈ s, f (Pi.mulSingle i (x i)) := by simp
    _ = f (fun i => if i ∈ s then x i else 1) :=
      (map_coordinate_truncation f.toMonoidHom s x).symm
    _ = f x := by
      simpa [finiteCoordinateFactor_apply] using f.finiteCoordinateFactor_restrict s hs x

/-- Taking the coefficients of an assembled family returns that same family. -/
@[simp]
theorem productCoefficients_dfinsuppProd
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) :
    (dfinsuppProd a).productCoefficients = a.toAdd := by
  ext i
  simp

/-- Continuous homomorphisms from a product of groups to a commutative group with
continuous multiplication and no small subgroups form the commutative monoid of
finitely supported families of continuous coordinate homomorphisms. -/
noncomputable def productDecomposition :
    ((∀ i, G i) →ₜ* D) ≃* Multiplicative (Π₀ i, Additive (G i →ₜ* D)) where
  toFun f := Multiplicative.ofAdd f.productCoefficients
  invFun := dfinsuppProd
  left_inv := dfinsuppProd_productCoefficients
  right_inv := by
    intro a
    exact congrArg Multiplicative.ofAdd (productCoefficients_dfinsuppProd a)
  map_mul' := by
    intro f g
    exact congrArg Multiplicative.ofAdd (productCoefficients_mul f g)

@[simp]
theorem productDecomposition_apply (f : (∀ i, G i) →ₜ* D) (i : ι) :
    (productDecomposition f).toAdd i = Additive.ofMul (f.coordinateHom i) :=
  productCoefficients_apply f i

@[simp]
theorem productDecomposition_symm_eq_dfinsuppProd
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) :
    productDecomposition.symm a = dfinsuppProd a := rfl

/-- The inverse equivalence is evaluated by a finite product on the original
coordinates. -/
theorem productDecomposition_symm_apply
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) (x : ∀ i, G i) :
    productDecomposition.symm a x = ∏ i ∈ a.toAdd.support, (a.toAdd i).toMul (x i) :=
  dfinsuppProd_apply a x

/-- Every finitely supported family extends uniquely, with no compatibility
conditions beyond commutativity of the target. -/
theorem existsUnique_coordinateHom
    (a : Multiplicative (Π₀ i, Additive (G i →ₜ* D))) :
    ∃! f : (∀ i, G i) →ₜ* D, ∀ i, f.coordinateHom i = (a.toAdd i).toMul := by
  refine ⟨productDecomposition.symm a, ?_, ?_⟩
  · intro i
    rw [productDecomposition_symm_eq_dfinsuppProd, coordinateHom_dfinsuppProd]
  · intro f hf
    apply (productDecomposition (G := G) (D := D)).injective
    calc
      productDecomposition f = a := by
        apply congrArg Multiplicative.ofAdd
        ext i
        simp [hf i]
      _ = productDecomposition (productDecomposition.symm a) :=
        ((productDecomposition (G := G) (D := D)).apply_symm_apply a).symm

end CommGroup

end ContinuousMonoidHom
