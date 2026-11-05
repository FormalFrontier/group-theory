/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Character.Extension
public import GroupTheory.Character.Cyclic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Order

/-!
# Separation by circle-valued characters

Circle characters separate points of any commutative group. A character detecting
an element is obtained on its cyclic subgroup and extended to the whole group.

For a supplied discrete topology these same homomorphisms are continuous. The
evaluation map here is only an unbundled function into the functions on all
continuous circle characters; no topological embedding or full duality is asserted.

## References

* R. Baer, *Abelian groups that are direct summands of every containing abelian
  group*, Bulletin of the American Mathematical Society 46 (1940), 800-806.
-/

@[expose] public section

universe u

variable {A : Type u} [CommGroup A]

namespace MonoidHom

/-- Every nonidentity element is detected by a circle character. -/
theorem exists_circle_apply_ne_one {a : A} (ha : a ≠ 1) :
    ∃ χ : A →* Circle, χ a ≠ 1 := by
  let H := Subgroup.zpowers a
  let g : H := ⟨a, Subgroup.mem_zpowers a⟩
  let : Nontrivial H := ⟨⟨g, 1, fun h => ha (congrArg Subtype.val h)⟩⟩
  have hg : ∀ x : H, x ∈ Subgroup.zpowers g := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
  obtain ⟨ψ, hψ⟩ := IsCyclic.exists_circleHom_apply_ne_one H hg
  obtain ⟨χ, hχ⟩ := exists_extend_circle H ψ
  refine ⟨χ, ?_⟩
  have heval : χ a = ψ g := congrArg (fun f : H →* Circle => f g) hχ
  simpa only [heval] using hψ

/-- Distinct elements are separated by a circle character. -/
theorem exists_circle_apply_ne {a b : A} (hab : a ≠ b) :
    ∃ χ : A →* Circle, χ a ≠ χ b := by
  obtain ⟨χ, hχ⟩ := exists_circle_apply_ne_one (a := a * b⁻¹)
    (by
      intro h
      apply hab
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using
        congrArg (fun x : A => x * b) h)
  refine ⟨χ, ?_⟩
  intro h
  apply hχ
  simp only [map_mul, map_inv, h, mul_inv_cancel]

end MonoidHom

namespace ContinuousMonoidHom

variable [TopologicalSpace A] [DiscreteTopology A]

/-- A character detecting a nonidentity element is continuous for a discrete topology. -/
theorem exists_circle_apply_ne_one {a : A} (ha : a ≠ 1) :
    ∃ χ : A →ₜ* Circle, χ a ≠ 1 := by
  obtain ⟨χ, hχ⟩ := MonoidHom.exists_circle_apply_ne_one ha
  exact ⟨⟨χ, continuous_of_discreteTopology⟩, hχ⟩

/-- Distinct points are separated by continuous circle characters in the discrete topology. -/
theorem exists_circle_apply_ne {a b : A} (hab : a ≠ b) :
    ∃ χ : A →ₜ* Circle, χ a ≠ χ b := by
  obtain ⟨χ, hχ⟩ := MonoidHom.exists_circle_apply_ne hab
  exact ⟨⟨χ, continuous_of_discreteTopology⟩, hχ⟩

/-- Evaluation on all continuous circle characters is injective for a discrete group. -/
theorem circle_eval_injective :
    Function.Injective (fun a : A => fun χ : A →ₜ* Circle => χ a) := by
  intro a b h
  by_contra hab
  obtain ⟨χ, hχ⟩ := exists_circle_apply_ne hab
  exact hχ (congrFun h χ)

end ContinuousMonoidHom
