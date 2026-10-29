/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Fixed vectors from generators

The fixed submodule of the original representation can be computed by imposing the
fixed-vector equations only on a generating set. Submonoid closure gives this
criterion for monoids. Subgroup closure gives the separate group criterion, even
when the coefficient module has no additive inverses.

The generated-set formulas intersect the equalizers of the action maps and
the identity. Their finite versions use `Finset.inf`, including its empty meet.
The free-monoid criterion uses generation by the original alphabet without a
finiteness or nonemptiness assumption. With additive-group coefficients, the
monoid computations can instead use kernels of differences of linear maps; the
scalar semiring need not be a ring.
-/

@[expose] public section

universe uR uG uM

namespace Representation

variable {R : Type uR} {G : Type uG} {M : Type uM}

section Monoid

variable [Semiring R] [Monoid G] [AddCommMonoid M] [Module R M]

/-- Equations fixing a vector propagate from a set to its submonoid closure. -/
theorem apply_eq_self_of_mem_submonoid_closure (ρ : Representation R G M)
    {S : Set G} {m : M} (hfix : ∀ g ∈ S, ρ g m = m)
    {g : G} (hg : g ∈ Submonoid.closure S) : ρ g m = m := by
  induction hg using Submonoid.closure_induction with
  | mem g hg => exact hfix g hg
  | one => exact congrArg (fun f : M →ₗ[R] M => f m) ρ.map_one
  | mul a b _ _ ha hb =>
    calc
      ρ (a * b) m = ρ a (ρ b m) :=
        congrArg (fun f : M →ₗ[R] M => f m) (ρ.map_mul a b)
      _ = m := by rw [hb, ha]

/-- A vector is fixed by a monoid representation exactly when its generators fix it. -/
theorem mem_fixedSubmodule_iff_of_submonoid_closure_eq_top
    (ρ : Representation R G M) (S : Set G) (hS : Submonoid.closure S = ⊤) (m : M) :
    m ∈ fixedSubmodule ρ ↔ ∀ g ∈ S, ρ g m = m := by
  constructor
  · intro hm g _
    exact (mem_fixedSubmodule ρ m).1 hm g
  · intro hfix
    apply (mem_fixedSubmodule ρ m).2
    intro g
    apply apply_eq_self_of_mem_submonoid_closure ρ hfix
    rw [hS]
    trivial

/-- Monoid generators compute the fixed submodule as an intersection of equalizers. -/
theorem fixedSubmodule_eq_iInf_eqLocus_of_submonoid_closure_eq_top
    (ρ : Representation R G M) (S : Set G) (hS : Submonoid.closure S = ⊤) :
    fixedSubmodule ρ = ⨅ g ∈ S, LinearMap.eqLocus (ρ g) LinearMap.id := by
  apply Submodule.ext
  intro m
  simpa only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] using
    mem_fixedSubmodule_iff_of_submonoid_closure_eq_top ρ S hS m

/-- A finite monoid generating set computes the fixed submodule by a finite meet,
with no nonempty-set assumption. -/
theorem fixedSubmodule_eq_finset_inf_eqLocus_of_submonoid_closure_eq_top
    (ρ : Representation R G M) (s : Finset G)
    (hs : Submonoid.closure (↑s : Set G) = ⊤) :
    fixedSubmodule ρ = s.inf (fun g => LinearMap.eqLocus (ρ g) LinearMap.id) := by
  classical
  rw [Finset.inf_eq_iInf]
  exact fixedSubmodule_eq_iInf_eqLocus_of_submonoid_closure_eq_top ρ (↑s : Set G) hs

end Monoid

section FreeMonoid

universe uA

variable {A : Type uA} [Semiring R] [AddCommMonoid M] [Module R M]

/-- For an arbitrary alphabet, a free-monoid representation fixes a vector exactly
when every letter fixes it. -/
theorem mem_fixedSubmodule_freeMonoid_iff (ρ : Representation R (FreeMonoid A) M)
    (m : M) :
    m ∈ fixedSubmodule ρ ↔ ∀ a : A, ρ (FreeMonoid.of a) m = m := by
  have hgen : Submonoid.closure (Set.range (FreeMonoid.of : A → FreeMonoid A)) = ⊤ :=
    FreeMonoid.closure_range_of
  refine (mem_fixedSubmodule_iff_of_submonoid_closure_eq_top ρ
    (Set.range (FreeMonoid.of : A → FreeMonoid A)) hgen m).trans ?_
  constructor
  · intro h a
    exact h (FreeMonoid.of a) ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    exact h a

end FreeMonoid

section Group

variable [Semiring R] [Group G] [AddCommMonoid M] [Module R M]

/-- Equations fixing a vector propagate to subgroup closure, without requiring
additive inverses in the coefficient module. -/
theorem apply_eq_self_of_mem_subgroup_closure (ρ : Representation R G M)
    {S : Set G} {m : M} (hfix : ∀ g ∈ S, ρ g m = m)
    {g : G} (hg : g ∈ Subgroup.closure S) : ρ g m = m := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hfix g hg
  | one => exact congrArg (fun f : M →ₗ[R] M => f m) ρ.map_one
  | mul a b _ _ ha hb =>
    calc
      ρ (a * b) m = ρ a (ρ b m) :=
        congrArg (fun f : M →ₗ[R] M => f m) (ρ.map_mul a b)
      _ = m := by rw [hb, ha]
  | inv a _ ha =>
    calc
      ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := congrArg (fun n : M => ρ a⁻¹ n) ha.symm
      _ = ρ (a⁻¹ * a) m :=
        (congrArg (fun f : M →ₗ[R] M => f m) (ρ.map_mul a⁻¹ a)).symm
      _ = m := by
        rw [inv_mul_cancel]
        exact congrArg (fun f : M →ₗ[R] M => f m) ρ.map_one

/-- Subgroup generators suffice to test membership in the original fixed submodule. -/
theorem mem_fixedSubmodule_iff_of_subgroup_closure_eq_top
    (ρ : Representation R G M) (S : Set G) (hS : Subgroup.closure S = ⊤) (m : M) :
    m ∈ fixedSubmodule ρ ↔ ∀ g ∈ S, ρ g m = m := by
  constructor
  · intro hm g _
    exact (mem_fixedSubmodule ρ m).1 hm g
  · intro hfix
    apply (mem_fixedSubmodule ρ m).2
    intro g
    apply apply_eq_self_of_mem_subgroup_closure ρ hfix
    rw [hS]
    trivial

/-- Subgroup generators compute the fixed submodule as an intersection of equalizers. -/
theorem fixedSubmodule_eq_iInf_eqLocus_of_subgroup_closure_eq_top
    (ρ : Representation R G M) (S : Set G) (hS : Subgroup.closure S = ⊤) :
    fixedSubmodule ρ = ⨅ g ∈ S, LinearMap.eqLocus (ρ g) LinearMap.id := by
  apply Submodule.ext
  intro m
  simpa only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply] using
    mem_fixedSubmodule_iff_of_subgroup_closure_eq_top ρ S hS m

/-- A finite subgroup generating set computes the fixed submodule by a
finite meet of equalizers, including the empty meet. -/
theorem fixedSubmodule_eq_finset_inf_eqLocus_of_subgroup_closure_eq_top
    (ρ : Representation R G M) (s : Finset G)
    (hs : Subgroup.closure (↑s : Set G) = ⊤) :
    fixedSubmodule ρ = s.inf (fun g => LinearMap.eqLocus (ρ g) LinearMap.id) := by
  classical
  rw [Finset.inf_eq_iInf]
  exact fixedSubmodule_eq_iInf_eqLocus_of_subgroup_closure_eq_top ρ (↑s : Set G) hs

end Group

section CoeffGroup

variable [Semiring R] [Monoid G] [AddCommGroup M] [Module R M]

/-- With additive-group coefficients, monoid generators compute fixed vectors by
kernels of differences; the scalar semiring need not be a ring. -/
theorem fixedSubmodule_eq_iInf_ker_sub_id_of_submonoid_closure_eq_top
    (ρ : Representation R G M) (S : Set G) (hS : Submonoid.closure S = ⊤) :
    fixedSubmodule ρ = ⨅ g ∈ S, LinearMap.ker (ρ g - LinearMap.id) := by
  apply Submodule.ext
  intro m
  simpa only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] using
    mem_fixedSubmodule_iff_of_submonoid_closure_eq_top ρ S hS m

/-- A finite monoid generating set computes the fixed submodule by a finite meet
of difference kernels over the original additive-group coefficient module. -/
theorem fixedSubmodule_eq_finset_inf_ker_sub_id_of_submonoid_closure_eq_top
    (ρ : Representation R G M) (s : Finset G)
    (hs : Submonoid.closure (↑s : Set G) = ⊤) :
    fixedSubmodule ρ = s.inf (fun g => LinearMap.ker (ρ g - LinearMap.id)) := by
  classical
  rw [Finset.inf_eq_iInf]
  exact fixedSubmodule_eq_iInf_ker_sub_id_of_submonoid_closure_eq_top ρ (↑s : Set G) hs

end CoeffGroup

end Representation
