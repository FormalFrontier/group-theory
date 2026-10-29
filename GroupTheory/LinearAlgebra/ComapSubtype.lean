/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map

/-!
# Naturality of comap–subtype equivalences

For submodules `P ≤ Q`, Mathlib's `Submodule.comapSubtypeEquivOfLe` identifies
vectors of `Q` lying in `P` with vectors of `P`. This identification is natural
for commuting squares between submodule inclusions. The maps on the larger
submodules need not extend to maps on the ambient modules.

The restricted map is a codomain restriction of the given map on `Q`. Its
membership proof comes from the inclusion square, not from transport through
the equivalences.
-/

@[expose] public section

set_option autoImplicit false

universe uR uM uN

namespace Submodule

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- The comap–subtype equivalences commute with a square of linear maps between
submodule inclusions. The map between the comaps is the restriction of `u`,
with membership derived from the given square. -/
theorem comapSubtypeEquivOfLe_naturality
    {P Q : Submodule R M} {P' Q' : Submodule R N}
    (i : P ≤ Q) (i' : P' ≤ Q')
    (u : Q →ₗ[R] Q') (v : P →ₗ[R] P')
    (h : u.comp (LinearMap.codRestrict Q P.subtype (fun x => i x.property)) =
      (LinearMap.codRestrict Q' P'.subtype (fun x => i' x.property)).comp v) :
    let uD : P.comap Q.subtype →ₗ[R] P'.comap Q'.subtype :=
      LinearMap.codRestrict (P'.comap Q'.subtype)
        (u.comp (P.comap Q.subtype).subtype)
        (by
          intro x
          have hx : (u x.val : N) = (v (comapSubtypeEquivOfLe i x) : N) :=
            congrArg
              (fun k : P →ₗ[R] Q' => (k (comapSubtypeEquivOfLe i x) : N)) h
          exact (show (u x.val : N) ∈ P' from
            hx.symm ▸ (v (comapSubtypeEquivOfLe i x)).property))
    (comapSubtypeEquivOfLe i').toLinearMap.comp uD =
      v.comp (comapSubtypeEquivOfLe i).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg
    (fun k : P →ₗ[R] Q' => (k (comapSubtypeEquivOfLe i x) : N)) h

end Submodule
