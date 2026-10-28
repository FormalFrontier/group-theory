/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.LinearAlgebra.Prod

/-!
# Products of submodules

`Submodule.prodEquiv` identifies the product submodule in the original product module
with the product of the two submodule types. Its coordinate formulas and inclusion
identity describe the equivalence without changing either factor's module structure.

This is a representation-independent linear-algebra supplement. It uses Mathlib's
`Submodule.prod`, `Submodule.mem_prod` and linear product-map API from
`Mathlib.LinearAlgebra.Span.Basic` and `Mathlib.LinearAlgebra.Prod`. The span and submodule
file is by Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric
Dupuis and Heather Macbeth; the linear product-map file is by Johannes Hölzl, Mario
Carneiro, Kevin Buzzard, Yury Kudryashov and Eric Wieser. The product module instances
are by Simon Hudon, Patrick Massot and Eric Wieser.
-/

@[expose] public section

universe uR uA uB

namespace Submodule

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [Semiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]

/-- Splitting coordinates identifies a product submodule with the product of its factors. -/
def prodEquiv (P : Submodule R A) (Q : Submodule R B) :
    (P.prod Q) ≃ₗ[R] P × Q where
  toFun z := (⟨(z : A × B).1, (mem_prod.mp z.property).1⟩,
    ⟨(z : A × B).2, (mem_prod.mp z.property).2⟩)
  invFun p := ⟨((p.1 : A), (p.2 : B)), mem_prod.mpr ⟨p.1.property, p.2.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl rfl
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' z w := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r z := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The first coordinate of the splitting equivalence is the original first coordinate. -/
@[simp]
theorem prodEquiv_apply_fst (P : Submodule R A) (Q : Submodule R B) (z : P.prod Q) :
    ((prodEquiv P Q z).1 : A) = (z : A × B).1 := rfl

/-- The second coordinate of the splitting equivalence is the original second coordinate. -/
@[simp]
theorem prodEquiv_apply_snd (P : Submodule R A) (Q : Submodule R B) (z : P.prod Q) :
    ((prodEquiv P Q z).2 : B) = (z : A × B).2 := rfl

/-- The inverse splitting equivalence joins the two original ambient coordinates. -/
@[simp]
theorem coe_prodEquiv_symm_apply (P : Submodule R A) (Q : Submodule R B) (p : P × Q) :
    ((prodEquiv P Q).symm p : A × B) = ((p.1 : A), (p.2 : B)) := rfl

/-- The splitting equivalence commutes with the inclusions into the original product module. -/
theorem subtype_prodMap_comp_prodEquiv (P : Submodule R A) (Q : Submodule R B) :
    (P.subtype.prodMap Q.subtype).comp (prodEquiv P Q).toLinearMap = (P.prod Q).subtype := by
  apply LinearMap.ext
  intro z
  change (((prodEquiv P Q z).1 : A), ((prodEquiv P Q z).2 : B)) = (z : A × B)
  exact Prod.ext (prodEquiv_apply_fst P Q z) (prodEquiv_apply_snd P Q z)

end Submodule
