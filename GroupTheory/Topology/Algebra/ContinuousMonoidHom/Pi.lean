/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Continuous homomorphisms from finite dependent products

For a finite family of monoids with topologies and a commutative topological group
`E`, restriction to the coordinates identifies the compact-open space of continuous
homomorphisms from the dependent product with the product of the factor hom spaces.
The inverse multiplies the coordinate values in `E`.

The source factors retain their original operations and topologies. They need not
be commutative or have continuous operations, and no source local compactness or
separation hypothesis is imposed. Coordinate inclusions and projections are defined
for arbitrary indices; the hom-space equivalence uses a finite index, including the
empty index. It does not describe duals of infinite products.

The algebraic inverse is Mathlib's `MonoidHom.noncommPiCoprodEquiv`, applied to the
family with its automatic commutation witness in `E`. The ordinary product formula
is the comparison `Finset.noncommProd_eq_prod`, not a product in the source monoids.
Fixed precomposition and finite products in the compact-open hom-space topological
group give the continuity of the two parameter maps.

## Main definitions

* `ContinuousMonoidHom.mulSingle`: the continuous identity-supported inclusion.
* `Pi.evalContinuousMonoidHom`: the continuous coordinate projection.
* `ContinuousMonoidHom.piEquiv`: restriction to a finite family of coordinates.

## References

* Mathlib's `GroupTheory.NoncommPiCoprod` (Joachim Breitner), for the algebraic
  universal property and its inverse data.
* Mathlib's `Data.Finset.NoncommProd` (Yakov Pechersky), for `MonoidHom.pi_ext`
  and comparison of noncommutative products with commutative products.
* Mathlib's `Algebra.Group.Pi.Lemmas` and `Algebra.BigOperators.Pi`
  (Simon Hudon and Patrick Massot), for coordinate homomorphisms and the stronger
  commutative-source equivalence `Pi.monoidHomMulEquiv`.
* Mathlib's `Topology.Constructions` (Johannes Hölzl, Mario Carneiro and
  Patrick Massot), for the original product topology and coordinate continuity.
* Mathlib's `Topology.Algebra.Group.CompactOpen` (Thomas Browning and Nailin Guan),
  for fixed precomposition and the topological-group structure on hom spaces.
-/

@[expose] public section

universe u v w z

open scoped BigOperators

namespace ContinuousMonoidHom

variable {I : Type u} (A : I → Type v)
variable [∀ i, Monoid (A i)] [∀ i, TopologicalSpace (A i)]

/-- The continuous inclusion supported at one coordinate, taking the value one
at every other coordinate. Its algebraic map is `MonoidHom.mulSingle`. -/
noncomputable def mulSingle (i : I) : A i →ₜ* (∀ j, A j) := by
  classical
  exact
    { toMonoidHom := MonoidHom.mulSingle A i
      continuous_toFun := continuous_mulSingle i }

/-- The coordinate inclusion has its prescribed value at its supporting index. -/
@[simp] theorem mulSingle_apply_same (i : I) (a : A i) :
    mulSingle A i a i = a := by
  classical
  exact Pi.mulSingle_eq_same i a

/-- The coordinate inclusion is one away from its supporting index. -/
@[simp] theorem mulSingle_apply_of_ne (i j : I) (a : A i) (h : j ≠ i) :
    mulSingle A i a j = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h a

end ContinuousMonoidHom

namespace Pi

variable {I : Type u} (A : I → Type v)
variable [∀ i, Monoid (A i)] [∀ i, TopologicalSpace (A i)]

/-- The continuous projection from a dependent product to one coordinate,
with algebraic map `Pi.evalMonoidHom`. -/
def evalContinuousMonoidHom (i : I) : (∀ j, A j) →ₜ* A i where
  toMonoidHom := Pi.evalMonoidHom A i
  continuous_toFun := continuous_apply i

/-- The continuous coordinate projection evaluates the original function. -/
@[simp] theorem evalContinuousMonoidHom_apply (i : I) (a : ∀ j, A j) :
    evalContinuousMonoidHom A i a = a i := rfl

/-- The continuous coordinate projection coerces to the algebraic projection. -/
@[simp] theorem coe_evalContinuousMonoidHom (i : I) :
    (evalContinuousMonoidHom A i : (∀ j, A j) →* A i) = Pi.evalMonoidHom A i := rfl

/-- Forgetting continuity recovers the coordinate projection homomorphism. -/
theorem evalContinuousMonoidHom_toMonoidHom (i : I) :
    (evalContinuousMonoidHom A i).toMonoidHom = Pi.evalMonoidHom A i := rfl

end Pi

namespace ContinuousMonoidHom

variable {I : Type u} (A : I → Type v)
variable [∀ i, Monoid (A i)] [∀ i, TopologicalSpace (A i)]

/-- Continuous homomorphisms from a finite dependent product are determined by
their restrictions to the identity-supported coordinate inclusions. -/
theorem pi_ext [Finite I] {E : Type w} [Monoid E] [TopologicalSpace E]
    {χ ψ : (∀ i, A i) →ₜ* E}
    (h : ∀ i, χ.comp (mulSingle A i) = ψ.comp (mulSingle A i)) : χ = ψ := by
  classical
  apply toMonoidHom_injective
  exact MonoidHom.pi_ext fun i a => congrArg (fun f : A i →ₜ* E => f a) (h i)

variable [Fintype I] (E : Type w)
variable [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]

private theorem noncommPiCoprod_eq_prod_toMonoidHom (c : ∀ i, A i →ₜ* E) :
    MonoidHom.noncommPiCoprod (fun i => (c i).toMonoidHom)
        (fun _ _ _ _ _ => Commute.all _ _) =
      (∏ i, (c i).comp (Pi.evalContinuousMonoidHom A i)).toMonoidHom := by
  classical
  apply MonoidHom.ext
  intro a
  have hprod (s : Finset I) :
      (∏ i ∈ s, (c i).comp (Pi.evalContinuousMonoidHom A i)) a =
        ∏ i ∈ s, c i (a i) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | insert i s hi ih =>
        simpa only [Finset.prod_insert hi, mul_apply, coe_comp, Function.comp_apply,
          Pi.evalContinuousMonoidHom_apply] using
          congrArg (fun z : E => c i (a i) * z) ih
  exact (Finset.noncommProd_eq_prod Finset.univ (fun i => c i (a i))).trans
    (hprod Finset.univ).symm

/-- Restriction to the coordinates is a continuous multiplicative equivalence
between compact-open hom spaces. Its inverse is the stock finite noncommutative
coproduct of the factor homomorphisms, whose values commute in `E`. -/
noncomputable def piEquiv :
    ((∀ i, A i) →ₜ* E) ≃ₜ* (∀ i, A i →ₜ* E) := by
  classical
  exact
    { toFun χ i := χ.comp (mulSingle A i)
      invFun c :=
        { toMonoidHom := MonoidHom.noncommPiCoprodEquiv
            ⟨fun i => (c i).toMonoidHom, fun _ _ _ _ _ => Commute.all _ _⟩
          continuous_toFun := by
            change Continuous (MonoidHom.noncommPiCoprod (fun i => (c i).toMonoidHom)
              (fun _ _ _ _ _ => Commute.all _ _))
            rw [noncommPiCoprod_eq_prod_toMonoidHom A E c]
            exact (∏ i, (c i).comp (Pi.evalContinuousMonoidHom A i)).continuous_toFun }
      left_inv := by
        intro χ
        apply toMonoidHom_injective
        exact (MonoidHom.noncommPiCoprodEquiv).apply_symm_apply χ.toMonoidHom
      right_inv := by
        intro c
        funext i
        apply ext
        intro a
        exact MonoidHom.noncommPiCoprod_mulSingle (fun i => (c i).toMonoidHom)
          (hcomm := fun _ _ _ _ _ => Commute.all _ _) i a
      map_mul' := by
        intro χ ψ
        funext i
        exact ext fun a => rfl
      continuous_toFun := continuous_pi fun i => continuous_comp_left (mulSingle A i)
      continuous_invFun := by
        have hprod : Continuous (fun c : ∀ i, A i →ₜ* E =>
            ∏ i, (c i).comp (Pi.evalContinuousMonoidHom A i)) :=
          continuous_finsetProd Finset.univ fun i _ =>
            (continuous_comp_left (C := E) (Pi.evalContinuousMonoidHom A i)).comp
              (continuous_apply i)
        apply hprod.congr
        intro c
        apply toMonoidHom_injective
        exact (noncommPiCoprod_eq_prod_toMonoidHom A E c).symm }

/-- The finite hom-space equivalence restricts along each coordinate inclusion. -/
@[simp] theorem piEquiv_apply (χ : (∀ i, A i) →ₜ* E) (i : I) :
    piEquiv A E χ i = χ.comp (mulSingle A i) := rfl

/-- The restricted character evaluates on the identity-supported inclusion. -/
theorem piEquiv_apply_apply (χ : (∀ i, A i) →ₜ* E) (i : I) (a : A i) :
    piEquiv A E χ i a = χ (mulSingle A i a) := rfl

/-- Forgetting continuity of the inverse gives Mathlib's noncommutative coproduct. -/
theorem piEquiv_symm_toMonoidHom (c : ∀ i, A i →ₜ* E) :
    ((piEquiv A E).symm c).toMonoidHom =
      MonoidHom.noncommPiCoprod (fun i => (c i).toMonoidHom)
        (fun _ _ _ _ _ => Commute.all _ _) := rfl

/-- The inverse multiplies the factor values in the commutative target. -/
theorem piEquiv_symm_apply_apply (c : ∀ i, A i →ₜ* E) (a : ∀ i, A i) :
    (piEquiv A E).symm c a = ∏ i, c i (a i) := by
  exact Finset.noncommProd_eq_prod Finset.univ (fun i => c i (a i))

/-- As a compact-open homomorphism, reconstruction is the finite product of
fixed pullbacks along the coordinate projections. -/
theorem piEquiv_symm_eq_prod (c : ∀ i, A i →ₜ* E) :
    (piEquiv A E).symm c = ∏ i, (c i).comp (Pi.evalContinuousMonoidHom A i) := by
  apply toMonoidHom_injective
  rw [piEquiv_symm_toMonoidHom]
  exact noncommPiCoprod_eq_prod_toMonoidHom A E c

/-- Reconstructing a family and restricting to a coordinate returns that factor. -/
@[simp] theorem piEquiv_symm_comp_mulSingle (c : ∀ i, A i →ₜ* E) (i : I) :
    ((piEquiv A E).symm c).comp (mulSingle A i) = c i := by
  exact congrFun ((piEquiv A E).apply_symm_apply c) i

/-- A homomorphism is reconstructed from a prescribed family exactly when its
coordinate restrictions are that family. -/
theorem piEquiv_symm_eq_iff (c : ∀ i, A i →ₜ* E) (χ : (∀ i, A i) →ₜ* E) :
    (piEquiv A E).symm c = χ ↔ ∀ i, χ.comp (mulSingle A i) = c i := by
  constructor
  · intro h i
    rw [← h]
    exact piEquiv_symm_comp_mulSingle A E c i
  · intro h
    apply (piEquiv A E).injective
    exact ((piEquiv A E).apply_symm_apply c).trans (funext h).symm

/-- Coordinate restriction commutes with fixed postcomposition. -/
theorem piEquiv_naturality {F : Type z} [CommGroup F] [TopologicalSpace F]
    [IsTopologicalGroup F] (f : E →ₜ* F) (χ : (∀ i, A i) →ₜ* E) (i : I) :
    piEquiv A F (f.comp χ) i = f.comp (piEquiv A E χ i) := rfl

end ContinuousMonoidHom
