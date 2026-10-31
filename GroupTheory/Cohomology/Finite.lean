/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import HomologicalAlgebra.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality and finiteness of group cohomology

Zeroth group cohomology has cardinality at most that of the coefficient representation,
for an arbitrary group and action. For finite coefficients this also bounds `Nat.card`,
and zeroth group cohomology has finite underlying carrier. For a finite group,
ordinary group cohomology has finite underlying carrier in every nonnegative degree.
The coefficient ring need not be finite.

In every nonnegative degree `n`, the cardinality is at most
`Cardinal.mk A ^ (Cardinal.mk G ^ n)`, without any finiteness assumption on the
group or coefficient carrier. This follows from the cardinality of the canonical
inhomogeneous cochains and the cardinal bound for module homology.
For finite groups and coefficients, the same estimate holds for `Nat.card`.

The degree-zero results use Mathlib's identification with the invariant coefficient
submodule, whose carrier embeds in the coefficient carrier. The all-degree finiteness
result uses finite inhomogeneous cochains and the finiteness of homology for a short
complex of modules with finite middle carrier.
-/

@[expose] public section

open CategoryTheory

universe u

namespace groupCohomology

variable {R G : Type u} [CommRing R] [Group G]

/-- Zeroth group cohomology has finite underlying carrier for finite coefficients. -/
instance finite_zero (A : Rep R G) [Finite A] : Finite (groupCohomology A 0) :=
  Finite.of_equiv _
    (((CategoryTheory.forget (ModuleCat R)).mapIso (H0Iso A)).toEquiv.symm)

/-- The cardinality of zeroth group cohomology is at most that of its coefficients. -/
theorem mk_zero_le (A : Rep R G) :
    Cardinal.mk (groupCohomology A 0) ≤ Cardinal.mk A := by
  let e := ((CategoryTheory.forget (ModuleCat R)).mapIso (H0Iso A)).toEquiv
  calc
    Cardinal.mk (groupCohomology A 0) = Cardinal.mk _ := Cardinal.mk_congr e
    _ ≤ Cardinal.mk A := Cardinal.mk_subtype_le _

/-- For finite coefficients, zeroth group cohomology has at most as many elements. -/
theorem card_zero_le (A : Rep R G) [Finite A] :
    Nat.card (groupCohomology A 0) ≤ Nat.card A := by
  let e := ((CategoryTheory.forget (ModuleCat R)).mapIso (H0Iso A)).toEquiv
  exact Nat.card_le_card_of_injective (fun x => (e x).val)
    (Subtype.val_injective.comp e.injective)

/-- Ordinary group cohomology is bounded in cardinality by its inhomogeneous cochains. -/
theorem mk_le (A : Rep R G) (n : ℕ) :
    Cardinal.mk (groupCohomology A n) ≤
      (Cardinal.mk A) ^ ((Cardinal.mk G) ^ n) := by
  calc
    Cardinal.mk (groupCohomology A n) ≤
        Cardinal.mk ((inhomogeneousCochains A).X n) :=
      ShortComplex.mk_homology_le ((inhomogeneousCochains A).sc n)
    _ = (Cardinal.mk A) ^ ((Cardinal.mk G) ^ n) := by
      simp

/-- Ordinary cohomology has finite carrier for a finite group and finite coefficient carrier. -/
instance finite {R G : Type u} [CommRing R] [Group G]
    (A : Rep.{u} R G) [Finite G] [Finite A] (n : ℕ) : Finite (groupCohomology A n) := by
  change Finite (((inhomogeneousCochains A).sc n).homology)
  have : Finite ((inhomogeneousCochains A).X n) := by
    dsimp [inhomogeneousCochains]
    infer_instance
  exact @ShortComplex.finite_homology_moduleCat R _ ((inhomogeneousCochains A).sc n) this

/-- For finite groups and coefficients, the cardinality of group cohomology is bounded by
that of the inhomogeneous cochains in the same degree. -/
theorem card_le (A : Rep R G) [Finite G] [Finite A] (n : ℕ) :
    Nat.card (groupCohomology A n) ≤ Nat.card A ^ (Nat.card G ^ n) := by
  have h := mk_le A n
  simp only [← Nat.cast_card] at h
  exact_mod_cast h

end groupCohomology
