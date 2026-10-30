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
for commuting squares of semilinear maps between submodule inclusions, with
source and target over possibly different scalar semirings. The maps on the
larger submodules need not extend to maps on the ambient modules.

The restricted map is a codomain restriction of the given map on `Q`. Its
membership proof comes from the inclusion square, not from transport through
the equivalences.
-/

@[expose] public section

set_option autoImplicit false

universe uR uS uM uN

namespace Submodule

variable {R : Type uR} [Semiring R] {S : Type uS} [Semiring S]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module S N]

/-- The comap–subtype equivalences commute with a square of `σ`-semilinear maps
between submodule inclusions over possibly different scalar semirings. The map
between the comaps is the restriction of `u`, with membership derived from the
given square. Each equivalence is linear over its own scalar semiring. -/
theorem comapSubtypeEquivOfLe_naturality
    {σ : R →+* S} {P Q : Submodule R M} {P' Q' : Submodule S N}
    (i : P ≤ Q) (i' : P' ≤ Q')
    (u : Q →ₛₗ[σ] Q') (v : P →ₛₗ[σ] P')
    (h : u.comp (LinearMap.codRestrict Q P.subtype (fun x => i x.property)) =
      (LinearMap.codRestrict Q' P'.subtype (fun x => i' x.property)).comp v) :
    let uD : P.comap Q.subtype →ₛₗ[σ] P'.comap Q'.subtype :=
      LinearMap.codRestrict (P'.comap Q'.subtype)
        (u.comp (P.comap Q.subtype).subtype)
        (by
          intro x
          have hx : (u x.val : N) = (v (comapSubtypeEquivOfLe i x) : N) :=
            congrArg
              (fun k : P →ₛₗ[σ] Q' => (k (comapSubtypeEquivOfLe i x) : N)) h
          exact (show (u x.val : N) ∈ P' from
            hx.symm ▸ (v (comapSubtypeEquivOfLe i x)).property))
    (comapSubtypeEquivOfLe i').toLinearMap.comp uD =
      v.comp (comapSubtypeEquivOfLe i).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact congrArg
    (fun k : P →ₛₗ[σ] Q' => (k (comapSubtypeEquivOfLe i x) : N)) h

end Submodule
