/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationLinHomAdd
public import GroupTheory.RepresentationNorm
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Finite-group intertwining lifts

For a finite group whose order is a unit in a semiring, an ordinary linear lift of
one intertwining map through another intertwining map can be replaced by an intertwining
lift. The semiring need not be commutative, and the coefficient modules need only be
additive commutative monoids.
Neither surjectivity of the map being lifted through nor equivariance of the given
linear lift is required.

The proof takes the norm in the additive conjugation representation on linear maps.
Division by the group order uses the inverse of the bijective `R`-linear natural-scalar
map on the codomain, not a pointwise `R`-module structure on linear maps.

## References

The averaging argument uses Mathlib's `Representation.norm`, its intertwining-map API,
and `LinearEquiv.ofBijective`, together with the additive conjugation and norm naturality
APIs. The related commutative-ring retraction construction in Mathlib is
`LinearMap.equivariantProjection` in `Mathlib.RepresentationTheory.Maschke`, by Kim
Morrison; here the given-lift statement uses representations over arbitrary semirings.
-/

@[expose] public section

universe uR uG uV uW uX

namespace Representation

/-- Over a semiring in which the finite group order is a unit, an ordinary linear lift
of one intertwining map through another intertwining map can be replaced by an
intertwining lift. -/
theorem exists_intertwining_lift
    {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW} {X : Type uX}
    [Semiring R] [Group G] [Finite G]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    [AddCommMonoid X] [Module R X]
    (ρV : Representation R G V) (ρW : Representation R G W)
    (ρX : Representation R G X)
    (hcard : IsUnit (Nat.card G : R))
    (q : Representation.IntertwiningMap ρW ρX)
    (h : Representation.IntertwiningMap ρV ρX)
    (l : V →ₗ[R] W)
    (hl : q.toLinearMap.comp l = h.toLinearMap) :
    ∃ f : Representation.IntertwiningMap ρV ρW, q.comp f = h := by
  classical
  let := Fintype.ofFinite G
  have hW : Function.Bijective (fun w : W => (Nat.card G) • w) := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (hcard.smul_bijective : Function.Bijective (fun w : W => (Nat.card G : R) • w))
  have hX : Function.Injective (fun x : X => (Nat.card G) • x) := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (hcard.smul_bijective : Function.Bijective (fun x : X => (Nat.card G : R) • x)).1
  let e : W ≃ₗ[R] W :=
    LinearEquiv.ofBijective ((Nat.card G) • (LinearMap.id : W →ₗ[R] W)) hW
  let l₀ : V →ₗ[R] W := e.symm.toLinearMap.comp l
  have hl₀ : (Nat.card G) • l₀ = l := by
    ext v
    exact e.apply_symm_apply (l v)
  let N : V →ₗ[R] W := norm (linHomAdd ρV ρW) l₀
  have hN : N ∈ (linHomAdd ρV ρW).fixedSubmodule :=
    (mem_fixedSubmodule _ _).2 (fun g => self_norm_apply _ g l₀)
  let f : IntertwiningMap ρV ρW :=
    { toLinearMap := N
      isIntertwining' := (mem_fixedSubmodule_linHomAdd_iff ρV ρW N).1 hN }
  refine ⟨f, ?_⟩
  have hh : h.toLinearMap ∈ (linHomAdd ρV ρX).fixedSubmodule :=
    (mem_fixedSubmodule_linHomAdd_iff ρV ρX _).2 h.isIntertwining'
  have hn : (Nat.card G) • N = norm (linHomAdd ρV ρW) l := by
    rw [← map_nsmul, hl₀]
  have heq : (Nat.card G) • (q.toLinearMap.comp N) =
      (Nat.card G) • h.toLinearMap := by
    calc
      (Nat.card G) • (q.toLinearMap.comp N) =
          q.toLinearMap.comp ((Nat.card G) • N) := by ext v; simp
      _ = q.toLinearMap.comp (norm (linHomAdd ρV ρW) l) := by rw [hn]
      _ = norm (linHomAdd ρV ρX) (q.toLinearMap.comp l) :=
        (IntertwiningMap.linHomAddPostcomp ρV ρW q).norm_comm_apply l
      _ = norm (linHomAdd ρV ρX) h.toLinearMap := by rw [hl]
      _ = (Nat.card G) • h.toLinearMap := by
        simpa only [Fintype.card_eq_nat_card] using
          norm_apply_coe_fixedSubmodule (linHomAdd ρV ρX) ⟨h.toLinearMap, hh⟩
  ext v
  apply hX
  exact congrArg (fun k : V →ₗ[R] X => k v) heq

end Representation
