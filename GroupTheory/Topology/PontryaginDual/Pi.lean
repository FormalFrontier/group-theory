/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Pi
public import GroupTheory.Topology.PontryaginDual

/-!
# Characters and canonical biduality of finite dependent products

Restriction to the identity-supported coordinate inclusions identifies the entire
compact-open Pontryagin dual of a finite dependent product with the product of the
factor duals. Reconstruction multiplies the coordinate character values in `Circle`.
The source factors need only be monoids with topologies.

Given canonical bidual equivalences of the factors, `PontryaginDual.piEvalEquiv`
constructs canonical biduality of their dependent product. Its forward map is
canonical evaluation. Its inverse uses the supplied factor inverses after twice
contravariant transport and coordinate restriction. The supplied factor data give
the continuity of evaluation, without additional source hypotheses.

The finite index may be empty. The comparisons retain the original product and
compact-open topologies; no infinite-product duality or general locally compact
abelian duality theorem is asserted.

## Main definitions

* `PontryaginDual.piEquiv`: finite-product duality by coordinate restriction.
* `PontryaginDual.piEvalEquiv`: canonical biduality from canonical factor biduality.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  (1.1.10)–(1.1.11), for the dual-group and canonical biduality setting.
* Mathlib's `Topology.Algebra.PontryaginDual`, for compact-open character spaces
  and their contravariant maps.
* Mathlib's `GroupTheory.NoncommPiCoprod` (Joachim Breitner) and
  `Data.Finset.NoncommProd` (Yakov Pechersky), for the finite algebraic universal
  property used by `ContinuousMonoidHom.piEquiv`.
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace PontryaginDual

variable {I : Type u} (A : I → Type v)
variable [∀ i, Monoid (A i)] [∀ i, TopologicalSpace (A i)]

/-- Characters of a finite dependent product are determined by their coordinate
restrictions. -/
theorem pi_ext [Finite I] {χ ψ : PontryaginDual (∀ i, A i)}
    (h : ∀ i, map (ContinuousMonoidHom.mulSingle A i) χ =
      map (ContinuousMonoidHom.mulSingle A i) ψ) : χ = ψ :=
  ContinuousMonoidHom.pi_ext A h

variable [Fintype I]

/-- Restriction identifies the compact-open dual of a finite dependent product
with the product of the compact-open factor duals. -/
noncomputable def piEquiv :
    PontryaginDual (∀ i, A i) ≃ₜ* (∀ i, PontryaginDual (A i)) :=
  ContinuousMonoidHom.piEquiv A Circle

/-- The finite dual comparison is the circle-valued hom-space equivalence. -/
theorem piEquiv_toContinuousMonoidHom :
    (piEquiv A : PontryaginDual (∀ i, A i) →ₜ* (∀ i, PontryaginDual (A i))) =
      ContinuousMonoidHom.toContinuousMonoidHom
        (ContinuousMonoidHom.piEquiv A Circle) := rfl

/-- The finite dual comparison restricts along each coordinate inclusion. -/
@[simp] theorem piEquiv_apply (χ : PontryaginDual (∀ i, A i)) (i : I) :
    piEquiv A χ i = map (ContinuousMonoidHom.mulSingle A i) χ := rfl

/-- Coordinate restriction evaluates on the original identity-supported inclusion. -/
theorem piEquiv_apply_apply (χ : PontryaginDual (∀ i, A i)) (i : I) (a : A i) :
    piEquiv A χ i a = χ (ContinuousMonoidHom.mulSingle A i a) := rfl

/-- The inverse dual comparison is the inverse circle-valued hom-space equivalence. -/
theorem piEquiv_symm_apply (c : ∀ i, PontryaginDual (A i)) :
    (piEquiv A).symm c = (ContinuousMonoidHom.piEquiv A Circle).symm c := rfl

/-- The reconstructed character multiplies the coordinate character values. -/
theorem piEquiv_symm_apply_apply (c : ∀ i, PontryaginDual (A i)) (a : ∀ i, A i) :
    (piEquiv A).symm c a = ∏ i, c i (a i) :=
  ContinuousMonoidHom.piEquiv_symm_apply_apply A Circle c a

/-- Reconstruction is the product of the characters pulled back along projections. -/
theorem piEquiv_symm_eq_prod (c : ∀ i, PontryaginDual (A i)) :
    (piEquiv A).symm c =
      ∏ i, map (Pi.evalContinuousMonoidHom A i) (c i) :=
  ContinuousMonoidHom.piEquiv_symm_eq_prod A Circle c

/-- Restriction commutes with the dual maps induced by a coordinatewise family
of continuous homomorphisms. The map on the original products uses
`MonoidHom.piMap` and the product topology. -/
theorem piEquiv_naturality {B : I → Type w}
    [∀ i, Monoid (B i)] [∀ i, TopologicalSpace (B i)]
    (f : ∀ i, A i →ₜ* B i) (χ : PontryaginDual (∀ i, B i)) :
    let F : (∀ i, A i) →ₜ* (∀ i, B i) :=
      { toMonoidHom := MonoidHom.piMap (fun i => (f i).toMonoidHom)
        continuous_toFun := continuous_pi fun i =>
          (f i).continuous.comp (continuous_apply i) }
    piEquiv A (map F χ) = fun i => map (f i) (piEquiv B χ i) := by
  classical
  dsimp only
  funext i
  apply PontryaginDual.ext
  intro a
  simp only [piEquiv_apply_apply, map_apply]
  congr 1
  funext j
  change f j (ContinuousMonoidHom.mulSingle A i a j) =
    ContinuousMonoidHom.mulSingle B i (f i a) j
  by_cases hji : j = i
  · subst j
    simp only [ContinuousMonoidHom.mulSingle_apply_same]
  · simp only [ContinuousMonoidHom.mulSingle_apply_of_ne A i j a hji,
      ContinuousMonoidHom.mulSingle_apply_of_ne B i j (f i a) hji, _root_.map_one]

/-- Twice-contravariant transport followed by restriction evaluates a bidual
character on a character supported at the chosen dual coordinate. -/
theorem piEquiv_mapEquiv_symm_apply
    (Φ : PontryaginDual (PontryaginDual (∀ i, A i))) (i : I)
    (χ : PontryaginDual (A i)) :
    ((mapEquiv (piEquiv A).symm).trans (piEquiv (fun i => PontryaginDual (A i))))
        Φ i χ =
      Φ ((piEquiv A).symm
        (ContinuousMonoidHom.mulSingle (fun i => PontryaginDual (A i)) i χ)) := rfl

/-- The bidual comparison sends canonical evaluation to coordinatewise canonical
evaluation. No continuity of evaluation in the original source point is assumed. -/
theorem piEquiv_mapEquiv_symm_evalHom (a : ∀ i, A i) :
    ((mapEquiv (piEquiv A).symm).trans (piEquiv (fun i => PontryaginDual (A i))))
        (evalHom (∀ i, A i) a) =
      fun i => evalHom (A i) (a i) := by
  classical
  funext i
  apply PontryaginDual.ext
  intro χ
  simp only [piEquiv_mapEquiv_symm_apply, evalHom_apply, piEquiv_symm_apply_apply]
  calc
    _ = ContinuousMonoidHom.mulSingle (fun i => PontryaginDual (A i)) i χ i (a i) := by
      apply Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
      intro j _ hji
      simpa only [one_apply] using
        congrArg (fun ψ : PontryaginDual (A j) => ψ (a j))
          (ContinuousMonoidHom.mulSingle_apply_of_ne
            (fun k => PontryaginDual (A k)) i j χ hji)
    _ = χ (a i) := by rw [ContinuousMonoidHom.mulSingle_apply_same]

private theorem piEquiv_mapEquiv_symm_evalHom_factor
    (e : ∀ i, A i ≃ₜ* PontryaginDual (PontryaginDual (A i)))
    (h : ∀ i (a : A i) (χ : PontryaginDual (A i)), e i a χ = χ a)
    (a : ∀ i, A i) :
    ((mapEquiv (piEquiv A).symm).trans (piEquiv (fun i => PontryaginDual (A i))))
        (evalHom (∀ i, A i) a) = fun i => e i (a i) := by
  rw [piEquiv_mapEquiv_symm_evalHom]
  funext i
  exact PontryaginDual.ext fun χ =>
    (evalHom_apply (a i) χ).trans ((h i (a i) χ).symm)

/-- Canonical biduality of a finite dependent product from canonical bidual
equivalences of its factors. The forward map is evaluation and the inverse uses
the supplied factor inverses after the finite dual comparisons. -/
noncomputable def piEvalEquiv
    (e : ∀ i, A i ≃ₜ* PontryaginDual (PontryaginDual (A i)))
    (h : ∀ i (a : A i) (χ : PontryaginDual (A i)), e i a χ = χ a) :
    (∀ i, A i) ≃ₜ* PontryaginDual (PontryaginDual (∀ i, A i)) :=
  let q := (mapEquiv (piEquiv A).symm).trans
    (piEquiv (fun i => PontryaginDual (A i)))
  { toFun := evalHom (∀ i, A i)
    invFun Φ := fun i => (e i).symm (q Φ i)
    left_inv := by
      intro a
      funext i
      have hq := congrFun (piEquiv_mapEquiv_symm_evalHom_factor A e h a) i
      exact (congrArg (e i).symm hq).trans ((e i).symm_apply_apply (a i))
    right_inv := by
      intro Φ
      apply q.injective
      calc
        q (evalHom (∀ i, A i) (fun i => (e i).symm (q Φ i))) =
            fun i => e i ((e i).symm (q Φ i)) :=
          piEquiv_mapEquiv_symm_evalHom_factor A e h _
        _ = q Φ := funext fun i => (e i).apply_symm_apply (q Φ i)
    map_mul' := _root_.map_mul (evalHom (∀ i, A i))
    continuous_toFun := by
      have hc : Continuous (fun a : ∀ i, A i => q.symm (fun i => e i (a i))) :=
        q.symm.continuous.comp
          (continuous_pi fun i => (e i).continuous.comp (continuous_apply i))
      exact hc.congr fun a => q.injective
        ((q.apply_symm_apply _).trans
          (piEquiv_mapEquiv_symm_evalHom_factor A e h a).symm)
    continuous_invFun := continuous_pi fun i =>
      (e i).symm.continuous.comp ((continuous_apply i).comp q.continuous) }

variable (e : ∀ i, A i ≃ₜ* PontryaginDual (PontryaginDual (A i)))
  (h : ∀ i (a : A i) (χ : PontryaginDual (A i)), e i a χ = χ a)

/-- Finite-product biduality coerces to the canonical evaluation homomorphism. -/
@[simp] theorem coe_piEvalEquiv :
    (piEvalEquiv A e h :
      (∀ i, A i) →* PontryaginDual (PontryaginDual (∀ i, A i))) =
        evalHom (∀ i, A i) := rfl

/-- Forgetting continuity of product biduality gives canonical evaluation. -/
theorem piEvalEquiv_toMonoidHom :
    (piEvalEquiv A e h :
      (∀ i, A i) →ₜ* PontryaginDual (PontryaginDual (∀ i, A i))).toMonoidHom =
        evalHom (∀ i, A i) := rfl

/-- Finite-product biduality evaluates each character at the given point. -/
theorem piEvalEquiv_apply (a : ∀ i, A i) (χ : PontryaginDual (∀ i, A i)) :
    piEvalEquiv A e h a χ = χ a := rfl

/-- The inverse of finite-product biduality uses the specified inverse in each
coordinate of the transported bidual character. -/
theorem piEvalEquiv_symm_apply (Φ : PontryaginDual (PontryaginDual (∀ i, A i))) :
    (piEvalEquiv A e h).symm Φ = fun i =>
      (e i).symm (((mapEquiv (piEquiv A).symm).trans
        (piEquiv (fun i => PontryaginDual (A i)))) Φ i) := rfl

/-- When a locally compact pair supplies the existing continuous evaluation map,
it is the continuous homomorphism underlying finite-product biduality. -/
theorem piEvalEquiv_toContinuousMonoidHom [LocallyCompactPair (∀ i, A i) Circle] :
    (piEvalEquiv A e h : (∀ i, A i) →ₜ*
      PontryaginDual (PontryaginDual (∀ i, A i))) = eval (∀ i, A i) := rfl

end PontryaginDual
