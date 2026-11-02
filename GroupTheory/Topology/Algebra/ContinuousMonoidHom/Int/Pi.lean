/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Int
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Pi
public import GroupTheory.Topology.TypeTags

/-!
# Continuous homomorphisms from finite products of integers

For a finite index type `I` and a commutative topological group `E`, evaluation
on the standard integer generators identifies the compact-open space
`Multiplicative (I → ℤ) →ₜ* E` with `I → E`. The inverse sends a tuple `c` to
the homomorphism taking `Multiplicative.ofAdd n` to `∏ i, c i ^ n i`.

The construction composes domain transport along `ContinuousMulEquiv.piMultiplicative`,
`ContinuousMonoidHom.piEquiv`, and the coordinatewise lift of
`ContinuousMonoidHom.intEvalEquiv`. Its inverse therefore retains the finite
noncommutative coproduct of the integer-power homomorphisms, precomposed with
the original tag equivalence. No new product or integer classification is used.

The source keeps its original Pi and type-tag topologies. No separation, local
compactness, nonempty index or discrete target is required. Commutativity of the
target is essential for unrestricted tuples of generator images. The empty
index is included. Product formulas carry an explicit `Fintype I`; the
constructor and generator laws require only `Finite I`.

## Main definitions

* `ContinuousMonoidHom.intPiEvalEquiv`: canonical integer-generator coordinates.

## References

* The finite-product and integer homomorphism equivalences in
  `GroupTheory.Topology.Algebra.ContinuousMonoidHom.Pi` and `.Int`, by
  Formal Frontier Agents, including their Mathlib references.
* Mathlib's `GroupTheory.NoncommPiCoprod` (Joachim Breitner), for the
  coproduct data, and `Data.Int.Cast.Lemmas` (Mario Carneiro), for `zpowersHom`.
* Mathlib's algebraic Pi congruence and the homeomorphism Pi congruence,
  lifted in `GroupTheory.Topology.Algebra.ContinuousMonoidHom`.
* The original dependent-product tag equivalence in `GroupTheory.Topology.TypeTags`.
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace ContinuousMonoidHom

section Ext

variable {I : Type u} [Finite I] {E : Type v} [Monoid E] [TopologicalSpace E]

/-- Homomorphisms from a finite product of integers are determined by the
images of the standard integer generators, in the original tagged Pi source. -/
theorem intPi_ext {χ ψ : Multiplicative (I → ℤ) →ₜ* E}
    (h : ∀ i, χ ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
        (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1))) =
      ψ ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
        (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1)))) :
    χ = ψ := by
  apply (ContinuousMulEquiv.continuousMonoidHomCongrLeftHomeomorph E
    (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ))).injective
  apply pi_ext (fun _ : I => Multiplicative ℤ)
  intro i
  apply toMonoidHom_injective
  exact MonoidHom.ext_mint (h i)

end Ext

variable (I : Type u) (E : Type v)
variable [CommGroup E] [TopologicalSpace E] [IsTopologicalGroup E]

section Finite

variable [Finite I]

/-- Evaluation on the standard integer generators is a continuous multiplicative
equivalence from the compact-open hom space of the original tagged finite Pi to
the tuples of a commutative topological group. The inverse uses the existing
finite coproduct and integer-power homomorphisms. -/
noncomputable def intPiEvalEquiv : (Multiplicative (I → ℤ) →ₜ* E) ≃ₜ* (I → E) := by
  letI := Fintype.ofFinite I
  exact
    ((ContinuousMulEquiv.continuousMonoidHomCongrLeft E
      (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ))).trans
      (piEquiv (fun _ : I => Multiplicative ℤ) E)).trans
      (ContinuousMulEquiv.piCongrRight fun _ : I => intEvalEquiv E)

/-- The coordinate of a homomorphism is its value at the corresponding standard
integer generator in the original source. -/
@[simp]
theorem intPiEvalEquiv_apply (χ : Multiplicative (I → ℤ) →ₜ* E) (i : I) :
    intPiEvalEquiv I E χ i =
      χ ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
        (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1))) := rfl

/-- Reconstruction takes the prescribed value on each integer generator. -/
@[simp]
theorem intPiEvalEquiv_symm_apply_generator (c : I → E) (i : I) :
    (intPiEvalEquiv I E).symm c
        ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
          (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1))) = c i :=
  congrFun ((intPiEvalEquiv I E).apply_symm_apply c) i

/-- A continuous homomorphism is reconstructed from its integer-generator values. -/
theorem intPiEvalEquiv_reconstruct (χ : Multiplicative (I → ℤ) →ₜ* E) :
    (intPiEvalEquiv I E).symm
      (fun i => χ ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
        (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1)))) = χ :=
  (intPiEvalEquiv I E).symm_apply_apply χ

/-- A homomorphism is the reconstruction of a tuple exactly when it takes the
prescribed values on the original integer generators. -/
theorem intPiEvalEquiv_symm_eq_iff (c : I → E) (χ : Multiplicative (I → ℤ) →ₜ* E) :
    (intPiEvalEquiv I E).symm c = χ ↔
      ∀ i, χ ((ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ)).symm
        (mulSingle (fun _ : I => Multiplicative ℤ) i (Multiplicative.ofAdd 1))) = c i := by
  constructor
  · intro h i
    rw [← h]
    exact intPiEvalEquiv_symm_apply_generator I E c i
  · intro h
    apply intPi_ext
    intro i
    exact (intPiEvalEquiv_symm_apply_generator I E c i).trans (h i).symm

variable {E} {F : Type w} [CommGroup F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- Integer-generator evaluation commutes with continuous target homomorphisms. -/
theorem intPiEvalEquiv_naturality (f : E →ₜ* F) (χ : Multiplicative (I → ℤ) →ₜ* E) :
    intPiEvalEquiv I F (f.comp χ) = fun i => f (intPiEvalEquiv I E χ i) := rfl

/-- Reconstruction of tuples commutes with continuous target homomorphisms. -/
theorem intPiEvalEquiv_symm_naturality (f : E →ₜ* F) (c : I → E) :
    (intPiEvalEquiv I F).symm (fun i => f (c i)) = f.comp ((intPiEvalEquiv I E).symm c) := by
  apply intPi_ext
  intro i
  simp only [intPiEvalEquiv_symm_apply_generator, coe_comp, Function.comp_apply]

end Finite

section Fintype

variable [Fintype I]

/-- With any finite enumeration, the classifier is the composite of domain
transport, the finite Pi hom-space equivalence, and coordinatewise integer evaluation.
Thus the chosen enumeration does not change the equivalence. -/
theorem intPiEvalEquiv_eq :
    intPiEvalEquiv I E =
      ((ContinuousMulEquiv.continuousMonoidHomCongrLeft E
        (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ))).trans
        (piEquiv (fun _ : I => Multiplicative ℤ) E)).trans
        (ContinuousMulEquiv.piCongrRight fun _ : I => intEvalEquiv E) := by
  ext χ i
  rfl

/-- The inverse is exactly the existing Pi reconstruction of the existing integer
homomorphisms, precomposed with the original dependent-product tag equivalence. -/
theorem intPiEvalEquiv_symm_apply (c : I → E) :
    (intPiEvalEquiv I E).symm c =
      ((piEquiv (fun _ : I => Multiplicative ℤ) E).symm
        (fun i => (intEvalEquiv E).symm (c i))).comp
        (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ) :
          Multiplicative (I → ℤ) →ₜ* (I → Multiplicative ℤ)) := by
  rw [intPiEvalEquiv_eq]
  rfl

/-- Forgetting continuity of reconstruction gives the same noncommutative Pi
coproduct of the same `zpowersHom` maps, followed by the tag homomorphism. -/
theorem intPiEvalEquiv_symm_toMonoidHom (c : I → E) :
    ((intPiEvalEquiv I E).symm c).toMonoidHom =
      (MonoidHom.noncommPiCoprod (fun i => zpowersHom E (c i))
        (fun _ _ _ _ _ => Commute.all _ _)).comp
        (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ) :
          Multiplicative (I → ℤ) →* (I → Multiplicative ℤ)) := by
  rw [intPiEvalEquiv_symm_apply]
  exact congrArg (fun g : (I → Multiplicative ℤ) →* E =>
      g.comp (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ) :
        Multiplicative (I → ℤ) →* (I → Multiplicative ℤ)))
    (piEquiv_symm_toMonoidHom (fun _ : I => Multiplicative ℤ) E
      (fun i => (intEvalEquiv E).symm (c i)))

/-- At a tagged integer tuple, reconstruction is the product of the prescribed
coordinate values raised to the corresponding integer powers. -/
@[simp]
theorem intPiEvalEquiv_symm_apply_ofAdd (c : I → E) (n : I → ℤ) :
    (intPiEvalEquiv I E).symm c (Multiplicative.ofAdd n) = ∏ i, c i ^ n i := by
  rw [intPiEvalEquiv_symm_apply]
  exact piEquiv_symm_apply_apply (fun _ : I => Multiplicative ℤ) E
    (fun i => (intEvalEquiv E).symm (c i))
    (ContinuousMulEquiv.piMultiplicative (fun _ : I => ℤ) (Multiplicative.ofAdd n))

/-- Every homomorphism on the original finite integer product is the product of
its generator values raised to the input coordinates. -/
theorem intPiEvalEquiv_apply_ofAdd (χ : Multiplicative (I → ℤ) →ₜ* E) (n : I → ℤ) :
    χ (Multiplicative.ofAdd n) = ∏ i, intPiEvalEquiv I E χ i ^ n i := by
  calc
    χ (Multiplicative.ofAdd n) =
        (intPiEvalEquiv I E).symm (intPiEvalEquiv I E χ) (Multiplicative.ofAdd n) :=
      congrArg (fun g : Multiplicative (I → ℤ) →ₜ* E => g (Multiplicative.ofAdd n))
        ((intPiEvalEquiv I E).symm_apply_apply χ).symm
    _ = ∏ i, intPiEvalEquiv I E χ i ^ n i :=
      intPiEvalEquiv_symm_apply_ofAdd I E (intPiEvalEquiv I E χ) n

end Fintype

end ContinuousMonoidHom
