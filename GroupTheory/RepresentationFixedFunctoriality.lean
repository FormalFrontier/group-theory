/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants

/-!
# Functoriality of fixed submodules

Equivariant semilinear maps transport fixed vectors, and injective maps identify the
source fixed submodule with the comap of the target fixed submodule. Restriction of a
representation along a monoid homomorphism enlarges its fixed submodule, with equality
for surjective homomorphisms and multiplicative equivalences.
-/

@[expose] public section

universe uR uS uG uH uV uW

namespace Representation

section Semilinear

variable {R : Type uR} {S : Type uS} {G : Type uG} {V : Type uV} {W : Type uW}
variable [Semiring R] [Semiring S] [Monoid G]
variable [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module S W]

/-- An equivariant semilinear map sends source fixed vectors into target fixed vectors. -/
theorem fixedSubmodule_le_comap (ρ : Representation R G V) (τ : Representation S G W)
    {σ : R →+* S} (u : V →ₛₗ[σ] W)
    (hu : ∀ (g : G) (v : V), u (ρ g v) = τ g (u v)) :
    ρ.fixedSubmodule ≤ (τ.fixedSubmodule).comap u := by
  intro v hv
  rw [Submodule.mem_comap, mem_fixedSubmodule]
  intro g
  calc
    τ g (u v) = u (ρ g v) := (hu g v).symm
    _ = u v := congrArg u ((mem_fixedSubmodule ρ v).1 hv g)

/-- The comap of the target fixed submodule along an injective equivariant semilinear
map is the source fixed submodule. -/
theorem comap_fixedSubmodule_eq_of_injective (ρ : Representation R G V)
    (τ : Representation S G W) {σ : R →+* S} (u : V →ₛₗ[σ] W)
    (hu : ∀ (g : G) (v : V), u (ρ g v) = τ g (u v))
    (hu_injective : Function.Injective u) :
    (τ.fixedSubmodule).comap u = ρ.fixedSubmodule := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_comap, mem_fixedSubmodule] at hv
    apply (mem_fixedSubmodule ρ v).2
    intro g
    apply hu_injective
    calc
      u (ρ g v) = τ g (u v) := hu g v
      _ = u v := hv g
  · exact fixedSubmodule_le_comap ρ τ u hu

end Semilinear

section Comp

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
variable [Semiring R] [Monoid G] [Monoid H] [AddCommMonoid V] [Module R V]

/-- Restricting a representation along a monoid homomorphism enlarges its fixed submodule. -/
theorem fixedSubmodule_le_comp (ρ : Representation R H V) (f : G →* H) :
    ρ.fixedSubmodule ≤ fixedSubmodule (ρ.comp f) := by
  intro v hv
  apply (mem_fixedSubmodule (ρ.comp f) v).2
  intro g
  simpa only [MonoidHom.comp_apply] using (mem_fixedSubmodule ρ v).1 hv (f g)

/-- Restriction along a surjective monoid homomorphism preserves the fixed submodule. -/
theorem fixedSubmodule_comp_eq_of_surjective (ρ : Representation R H V) (f : G →* H)
    (hf : Function.Surjective f) : fixedSubmodule (ρ.comp f) = ρ.fixedSubmodule := by
  apply le_antisymm
  · intro v hv
    apply (mem_fixedSubmodule ρ v).2
    intro h
    obtain ⟨g, rfl⟩ := hf h
    simpa only [MonoidHom.comp_apply] using
      (mem_fixedSubmodule (ρ.comp f) v).1 hv g
  · exact fixedSubmodule_le_comp ρ f

/-- Restriction along a multiplicative equivalence preserves the fixed submodule. -/
theorem fixedSubmodule_comp_mulEquiv (ρ : Representation R H V) (e : G ≃* H) :
    fixedSubmodule (ρ.comp e.toMonoidHom) = ρ.fixedSubmodule := by
  exact fixedSubmodule_comp_eq_of_surjective ρ e.toMonoidHom e.surjective

end Comp

end Representation
