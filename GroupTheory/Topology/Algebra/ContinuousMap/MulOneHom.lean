/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Compact

/-!
# Continuous maps preserving one and multiplication

The continuous maps preserving one and multiplication are closed under pointwise
one, products and inverses under the corresponding target assumptions. For a
commutative topological group target they form a subgroup of `C(M, D)` with carrier
`ContinuousMap.mulOneHomLocus M D`. The original subtype inherits its pointwise
group and topological group structures without changing its compact-open topology.
No continuity of the source operations is assumed.
-/

@[expose] public section

universe u v

namespace ContinuousMap

variable (M : Type u) (D : Type v)
variable [MulOneClass M] [TopologicalSpace M] [TopologicalSpace D]

section One

variable [MulOneClass D]

theorem one_mem_mulOneHomLocus : (1 : C(M, D)) ∈ mulOneHomLocus M D := by
  constructor <;> simp

@[ext] theorem mulOneHomLocus_ext {f g : ↥(mulOneHomLocus M D)}
    (h : ∀ x, (f : C(M, D)) x = (g : C(M, D)) x) : f = g :=
  Subtype.ext (ContinuousMap.ext h)

end One

section Mul

variable [CommMonoid D] [ContinuousMul D]

theorem mul_mem_mulOneHomLocus {f g : C(M, D)}
    (hf : f ∈ mulOneHomLocus M D) (hg : g ∈ mulOneHomLocus M D) :
    f * g ∈ mulOneHomLocus M D := by
  constructor
  · simpa using congrArg₂ (· * ·) hf.1 hg.1
  · intro x y
    simpa [hf.2, hg.2] using mul_mul_mul_comm (f x) (f y) (g x) (g y)

end Mul

section Inv

variable [CommGroup D] [ContinuousInv D]

theorem inv_mem_mulOneHomLocus {f : C(M, D)} (hf : f ∈ mulOneHomLocus M D) :
    f⁻¹ ∈ mulOneHomLocus M D := by
  constructor
  · simpa using congrArg (fun x : D => x⁻¹) hf.1
  · intro x y
    simp [hf.2, mul_comm]

end Inv

section Group

variable [CommGroup D] [IsTopologicalGroup D]

/-- Continuous maps preserving one and multiplication as a pointwise subgroup. -/
def mulOneHomSubgroup : Subgroup C(M, D) where
  carrier := mulOneHomLocus M D
  one_mem' := one_mem_mulOneHomLocus M D
  mul_mem' := mul_mem_mulOneHomLocus M D
  inv_mem' := inv_mem_mulOneHomLocus M D

@[simp] theorem mem_mulOneHomSubgroup (f : C(M, D)) :
    f ∈ mulOneHomSubgroup M D ↔ f 1 = 1 ∧ ∀ x y : M, f (x * y) = f x * f y :=
  Iff.rfl

@[simp] theorem coe_mulOneHomSubgroup :
    (mulOneHomSubgroup M D : Set C(M, D)) = mulOneHomLocus M D := rfl

/-- The original multiplicative-map locus has pointwise commutative group data. -/
instance mulOneHomLocusCommGroup : CommGroup ↥(mulOneHomLocus M D) :=
  inferInstanceAs (CommGroup ↥(mulOneHomSubgroup M D))

/-- The original compact-open subtype is a topological group. -/
instance mulOneHomLocusIsTopologicalGroup :
    IsTopologicalGroup ↥(mulOneHomLocus M D) :=
  inferInstanceAs (IsTopologicalGroup ↥(mulOneHomSubgroup M D))

namespace mulOneHomSubgroup

variable {M D}

@[simp] theorem coe_one :
    ((1 : ↥(mulOneHomLocus M D)) : C(M, D)) = 1 := rfl

@[simp] theorem coe_mul (f g : ↥(mulOneHomLocus M D)) :
    ((f * g : ↥(mulOneHomLocus M D)) : C(M, D)) =
      (f : C(M, D)) * (g : C(M, D)) := rfl

@[simp] theorem coe_inv (f : ↥(mulOneHomLocus M D)) :
    ((f⁻¹ : ↥(mulOneHomLocus M D)) : C(M, D)) = (f : C(M, D))⁻¹ := rfl

end mulOneHomSubgroup

end Group

end ContinuousMap
