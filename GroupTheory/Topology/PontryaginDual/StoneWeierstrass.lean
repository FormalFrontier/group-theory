/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Uniform density of scalar Pontryagin characters

A point-separating subgroup of the Pontryagin dual of a compact monoid has
complex linear span dense in the continuous complex-valued functions. The
characters are the original continuous `Circle`-valued monoid homomorphisms,
composed with the coercion `Circle → ℂ`.

The scalar characters form a multiplicative monoid containing one. Inversion
in the subgroup gives closure under complex conjugation, so their algebraic
span is a star subalgebra. Density then follows from Mathlib's scalar
Stone–Weierstrass theorem in the existing topology on `C(K, ℂ)`, which is the
uniform topology for compact `K`.

## References

* Mathlib's `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`
  supplies the scalar Stone–Weierstrass theorem.
* Mathlib's `Algebra.adjoin_eq_span` and the proof of
  `span_fourier_closure_eq_top` in `Analysis.Fourier.AddCircle` supply the
  algebraic-span bridge and its continuous-map closure formulation.
-/

@[expose] public section

universe u

namespace PontryaginDual

/-- If a subgroup of continuous circle-valued characters separates points of a
compact monoid, the complex linear span of its scalar characters is uniformly
dense in `C(K, ℂ)`. This is a bridge to the scalar Stone–Weierstrass theorem;
it needs neither a measure nor separation or countability assumptions on `K`. -/
theorem topologicalClosure_span_eq_top_of_separatesPoints
    {K : Type u} [Monoid K] [TopologicalSpace K] [CompactSpace K]
    (S : Subgroup (PontryaginDual K))
    (hS : ∀ x y : K, x ≠ y → ∃ χ ∈ S, χ x ≠ χ y) :
    (Submodule.span ℂ
      {f : C(K, ℂ) | ∃ χ ∈ S, ∀ x, f x = (χ x : ℂ)}).topologicalClosure = ⊤ := by
  let M : Submonoid C(K, ℂ) :=
    { carrier := {f | ∃ χ ∈ S, ∀ x, f x = (χ x : ℂ)}
      one_mem' := ⟨1, S.one_mem, fun x => by simp⟩
      mul_mem' := by
        rintro f g ⟨χ, hχ, hf⟩ ⟨ψ, hψ, hg⟩
        refine ⟨χ * ψ, S.mul_mem hχ hψ, fun x => ?_⟩
        rw [ContinuousMap.mul_apply, hf, hg]
        change (χ x : ℂ) * (ψ x : ℂ) = ((χ x * ψ x : Circle) : ℂ)
        exact (Circle.coe_mul (χ x) (ψ x)).symm }
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { toSubalgebra := Algebra.adjoin ℂ (M : Set C(K, ℂ))
      star_mem' := by
        change Algebra.adjoin ℂ (M : Set C(K, ℂ)) ≤
          star (Algebra.adjoin ℂ (M : Set C(K, ℂ)))
        refine Algebra.adjoin_le ?_
        rintro f ⟨χ, hχ, hf⟩
        refine Algebra.subset_adjoin ⟨χ⁻¹, S.inv_mem hχ, fun x => ?_⟩
        rw [ContinuousMap.star_apply, hf]
        exact (Circle.coe_inv_eq_conj (χ x)).symm }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hχ, hχxy⟩ := hS x y hxy
    let f : C(K, ℂ) :=
      (ContinuousMap.subtypeVal (Metric.sphere (0 : ℂ) 1)).comp χ.toContinuousMap
    have hf : f ∈ A := Algebra.subset_adjoin ⟨χ, hχ, fun _ => rfl⟩
    exact ⟨f, ⟨f, hf, rfl⟩, fun h => hχxy (Circle.coe_injective h)⟩
  have hspan : A.toSubalgebra.toSubmodule =
      Submodule.span ℂ (M : Set C(K, ℂ)) := by
    change (Algebra.adjoin ℂ (M : Set C(K, ℂ))).toSubmodule = _
    rw [Algebra.adjoin_eq_span, Submonoid.closure_eq]
  change (Submodule.span ℂ (M : Set C(K, ℂ))).topologicalClosure = ⊤
  rw [← hspan]
  exact congrArg (fun B : StarSubalgebra ℂ C(K, ℂ) => B.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA)

end PontryaginDual
