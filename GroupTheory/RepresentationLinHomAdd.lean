/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants

/-!
# Additive representations on linear maps

Conjugation acts on the additive monoid of linear maps over any semiring, including a
noncommutative semiring. We regard this as a representation over `ℕ`: no pointwise action
of the coefficient semiring on its linear maps is needed. Fixed vectors are exactly
intertwining maps, and postcomposition by an intertwining map is equivariant.

Over a commutative semiring the action agrees with Mathlib's `Representation.linHom`
after restricting scalars to `ℕ`.

## References

The conjugation construction follows Mathlib's `Representation.linHom` in
`Mathlib.RepresentationTheory.Basic`, by Antoine Labelle. We use the intertwining-map
API of Stepan Nesterov and Edison Xie and the fixed-submodule API.
-/

@[expose] public section

universe uR uG uV uW uX uY

namespace Representation

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
  {X : Type uX} {Y : Type uY}

section Semiring

variable [Semiring R] [Group G]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
  (ρV : Representation R G V) (ρW : Representation R G W)
  {ρX : Representation R G X} {ρY : Representation R G Y}

/-- Conjugation on `R`-linear maps, as a representation over `ℕ`.
Unlike `Representation.linHom`, this requires no commutativity of `R`. -/
def linHomAdd : Representation ℕ G (V →ₗ[R] W) where
  toFun g :=
    { toFun := fun f => (ρW g).comp (f.comp (ρV g⁻¹))
      map_add' := fun f₁ f₂ => by simp [LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun n f => by ext v; simp }
  map_one' := by ext f v; simp
  map_mul' g h := by
    ext f v
    simp [Module.End.mul_apply, mul_inv_rev]

/-- The conjugation action on a linear map. -/
@[simp]
theorem linHomAdd_apply (g : G) (f : V →ₗ[R] W) :
    linHomAdd ρV ρW g f = (ρW g).comp (f.comp (ρV g⁻¹)) := rfl

/-- Evaluation of the conjugation action. -/
theorem linHomAdd_apply_apply (g : G) (f : V →ₗ[R] W) (v : V) :
    linHomAdd ρV ρW g f v = ρW g (f (ρV g⁻¹ v)) := rfl

/-- A linear map is fixed under conjugation exactly when it intertwines the actions. -/
theorem mem_fixedSubmodule_linHomAdd_iff (f : V →ₗ[R] W) :
    f ∈ (linHomAdd ρV ρW).fixedSubmodule ↔
      ∀ g : G, f.comp (ρV g) = (ρW g).comp f := by
  rw [mem_fixedSubmodule]
  constructor
  · intro hf g
    ext v
    have hv := congrArg (fun k : V →ₗ[R] W => k (ρV g v)) (hf g)
    simpa using hv.symm
  · intro hf g
    ext v
    have hv := congrArg (fun k : V →ₗ[R] W => k (ρV g⁻¹ v)) (hf g)
    simpa using hv.symm

namespace IntertwiningMap

/-- Postcomposition by an intertwining map on additive Hom representations. -/
def linHomAddPostcomp (q : IntertwiningMap ρW ρX) :
    IntertwiningMap (linHomAdd ρV ρW) (linHomAdd ρV ρX) where
  toLinearMap :=
    { toFun := fun f => q.toLinearMap.comp f
      map_add' := fun f₁ f₂ => LinearMap.comp_add _ _ _
      map_smul' := fun n f => by ext v; simp }
  isIntertwining' g := by
    ext f v
    exact congrArg (fun k : W →ₗ[R] X => k (f (ρV g⁻¹ v))) (q.isIntertwining' g)

/-- Postcomposition acts by ordinary composition of linear maps. -/
@[simp]
theorem linHomAddPostcomp_apply (q : IntertwiningMap ρW ρX) (f : V →ₗ[R] W) :
    linHomAddPostcomp ρV ρW q f = q.toLinearMap.comp f := rfl

/-- Postcomposition by the identity is the identity. -/
@[simp]
theorem linHomAddPostcomp_id :
    linHomAddPostcomp ρV ρW (id ρW) = id (linHomAdd ρV ρW) := by
  ext f v
  rfl

/-- Postcomposition preserves composition of intertwining maps. -/
@[simp]
theorem linHomAddPostcomp_comp (q : IntertwiningMap ρW ρX)
    (p : IntertwiningMap ρX ρY) :
    linHomAddPostcomp ρV ρW (p.comp q) =
      (linHomAddPostcomp ρV ρX p).comp (linHomAddPostcomp ρV ρW q) := by
  ext f v
  rfl

end IntertwiningMap

end Semiring

section CommSemiring

variable [CommSemiring R] [Group G]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  (ρV : Representation R G V) (ρW : Representation R G W)

/-- Over a commutative semiring, additive conjugation is Mathlib's linear conjugation
with scalars restricted to `ℕ`. -/
theorem linHomAdd_apply_eq_restrictScalars (g : G) :
    linHomAdd ρV ρW g = (linHom ρV ρW g).restrictScalars ℕ := by
  ext f v
  rfl

end CommSemiring

end Representation
