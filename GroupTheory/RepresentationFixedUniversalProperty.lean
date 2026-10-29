/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants

/-!
# The universal property of fixed vectors

Intertwining maps from the trivial representation on an `R`-module `M` to a
representation `ρ` are additively equivalent to linear maps from `M` to
`ρ.fixedSubmodule`. The equivalence retains the underlying values and is
characterized by composition with the fixed-submodule inclusion. It is natural
in an intertwining map on the target.

For the regular left module `R`, this equivalence identifies incoming
intertwining maps with fixed vectors by evaluation at one. The inverse sends a
fixed vector `v` to the map `r ↦ r • v`.

Only a semiring, a monoid and additive commutative coefficient monoids are
required. The equivalences are additive and do not require pointwise
`R`-module structures on the spaces of linear maps or intertwining maps.
-/

@[expose] public section

universe uR uG uM uV uW

namespace Representation

variable {R : Type uR} {G : Type uG}
variable [Semiring R] [Monoid G]

section TrivialSource

variable {M : Type uM} {V : Type uV}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid V] [Module R V]

/-- Intertwining maps from the trivial representation are precisely linear maps
into the fixed submodule, with the same underlying values. -/
def trivialIntertwiningMapEquiv (ρ : Representation R G V) :
    IntertwiningMap (Representation.trivial R G M) ρ ≃+
      (M →ₗ[R] ρ.fixedSubmodule) where
  toFun K :=
    LinearMap.codRestrict ρ.fixedSubmodule K.toLinearMap (by
      intro m
      apply (mem_fixedSubmodule ρ (K m)).2
      intro g
      simpa using
        (Representation.IntertwiningMap.isIntertwining
          (Representation.trivial R G M) ρ K g m).symm)
  invFun L :=
    ⟨ρ.fixedSubmodule.subtype.comp L, by
      intro g
      ext m
      simp⟩
  left_inv K := by
    ext m
    simp
  right_inv L := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp
  map_add' K L := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    simp

/-- The forward equivalence factors the original underlying linear map through
the fixed-submodule inclusion. -/
theorem subtype_comp_trivialIntertwiningMapEquiv (ρ : Representation R G V)
    (K : IntertwiningMap (Representation.trivial R G M) ρ) :
    ρ.fixedSubmodule.subtype.comp (trivialIntertwiningMapEquiv ρ K) =
      K.toLinearMap := by
  exact LinearMap.subtype_comp_codRestrict (f := K.toLinearMap) ρ.fixedSubmodule _

/-- The underlying linear map of the inverse is the inclusion composed with the
given fixed-valued linear map. -/
theorem trivialIntertwiningMapEquiv_symm_toLinearMap (ρ : Representation R G V)
    (L : M →ₗ[R] ρ.fixedSubmodule) :
    ((trivialIntertwiningMapEquiv ρ).symm L).toLinearMap =
      ρ.fixedSubmodule.subtype.comp L := rfl

/-- Passing to the fixed submodule preserves every ambient value. -/
@[simp]
theorem trivialIntertwiningMapEquiv_apply (ρ : Representation R G V)
    (K : IntertwiningMap (Representation.trivial R G M) ρ) (m : M) :
    (trivialIntertwiningMapEquiv ρ K m : V) = K m := by
  have h := congrArg (fun t : M →ₗ[R] V => t m)
    (subtype_comp_trivialIntertwiningMapEquiv ρ K)
  simpa using h

/-- The inverse equivalence composes with the fixed-submodule inclusion. -/
@[simp]
theorem trivialIntertwiningMapEquiv_symm_apply (ρ : Representation R G V)
    (L : M →ₗ[R] ρ.fixedSubmodule) (m : M) :
    (trivialIntertwiningMapEquiv ρ).symm L m = (L m : V) := by
  have h := congrArg (fun t : M →ₗ[R] V => t m)
    (trivialIntertwiningMapEquiv_symm_toLinearMap ρ L)
  simpa using h

/-- Composition with the inclusion characterizes the linear map corresponding
to an incoming intertwining map. -/
theorem trivialIntertwiningMapEquiv_eq_iff (ρ : Representation R G V)
    (K : IntertwiningMap (Representation.trivial R G M) ρ)
    (L : M →ₗ[R] ρ.fixedSubmodule) :
    trivialIntertwiningMapEquiv ρ K = L ↔
      ρ.fixedSubmodule.subtype.comp L = K.toLinearMap := by
  constructor
  · intro h
    rw [← h]
    exact subtype_comp_trivialIntertwiningMapEquiv ρ K
  · intro h
    symm
    exact fixedSubmodule_codRestrict_unique ρ K.toLinearMap
      (fun g m => by
        simpa using
          (Representation.IntertwiningMap.isIntertwining
            (Representation.trivial R G M) ρ K g m).symm)
      L h

/-- The inclusion equation reconstructs the same incoming intertwining map. -/
theorem trivialIntertwiningMapEquiv_symm_eq_iff (ρ : Representation R G V)
    (L : M →ₗ[R] ρ.fixedSubmodule)
    (K : IntertwiningMap (Representation.trivial R G M) ρ) :
    (trivialIntertwiningMapEquiv ρ).symm L = K ↔
      ρ.fixedSubmodule.subtype.comp L = K.toLinearMap := by
  constructor
  · intro h
    rw [← h, trivialIntertwiningMapEquiv_symm_toLinearMap]
  · intro h
    have hL := (trivialIntertwiningMapEquiv_eq_iff ρ K L).2 h
    calc
      (trivialIntertwiningMapEquiv ρ).symm L =
          (trivialIntertwiningMapEquiv ρ).symm
            (trivialIntertwiningMapEquiv ρ K) :=
        congrArg (trivialIntertwiningMapEquiv ρ).symm hL.symm
      _ = K := (trivialIntertwiningMapEquiv ρ).symm_apply_apply K

section Naturality

variable {W : Type uW} [AddCommMonoid W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- The classification is natural in the given target intertwining map and its
map on fixed submodules. -/
theorem trivialIntertwiningMapEquiv_naturality (f : IntertwiningMap ρ σ)
    (K : IntertwiningMap (Representation.trivial R G M) ρ) :
    trivialIntertwiningMapEquiv σ (f.comp K) =
      f.fixedSubmoduleMap.comp (trivialIntertwiningMapEquiv ρ K) := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  simp only [trivialIntertwiningMapEquiv_apply, LinearMap.comp_apply,
    IntertwiningMap.fixedSubmoduleMap_apply, IntertwiningMap.comp_apply]

end Naturality

end TrivialSource

section RegularSource

variable {V : Type uV} [AddCommMonoid V] [Module R V]

/-- Incoming intertwining maps from the trivial representation on the regular
left module `R` correspond to fixed vectors by evaluation at one. This is the
regular-source specialization of `trivialIntertwiningMapEquiv`. -/
def trivialIntertwiningMapEquivSelf (ρ : Representation R G V) :
    IntertwiningMap (Representation.trivial R G R) ρ ≃+ ρ.fixedSubmodule where
  toFun K := trivialIntertwiningMapEquiv (M := R) ρ K 1
  invFun v :=
    (trivialIntertwiningMapEquiv (M := R) ρ).symm
      ({ toFun := fun r : R => r • v
         map_add' := fun r s => add_smul r s v
         map_smul' := by
           intro r s
           simpa using (mul_smul r s v) } : R →ₗ[R] ρ.fixedSubmodule)
  left_inv K := by
    apply (trivialIntertwiningMapEquiv (M := R) ρ).injective
    rw [AddEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro r
    change r • (trivialIntertwiningMapEquiv (M := R) ρ K) 1 =
      (trivialIntertwiningMapEquiv (M := R) ρ K) r
    simpa only [smul_eq_mul, mul_one] using
      ((trivialIntertwiningMapEquiv (M := R) ρ K).map_smul r (1 : R)).symm
  right_inv v := by
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    change (1 : R) • v = v
    exact one_smul R v
  map_add' K L := by
    simpa only [LinearMap.add_apply] using
      congrArg (fun F : R →ₗ[R] ρ.fixedSubmodule => F 1)
        ((trivialIntertwiningMapEquiv (M := R) ρ).map_add K L)

/-- The regular-source equivalence evaluates the original map at one. -/
@[simp]
theorem trivialIntertwiningMapEquivSelf_apply (ρ : Representation R G V)
    (K : IntertwiningMap (Representation.trivial R G R) ρ) :
    (trivialIntertwiningMapEquivSelf ρ K : V) = K 1 := by
  change (trivialIntertwiningMapEquiv (M := R) ρ K 1 : V) = K 1
  exact trivialIntertwiningMapEquiv_apply ρ K 1

/-- The inverse regular-source equivalence sends a fixed vector to its scalar
multiples in the original target module. -/
@[simp]
theorem trivialIntertwiningMapEquivSelf_symm_apply (ρ : Representation R G V)
    (v : ρ.fixedSubmodule) (r : R) :
    (trivialIntertwiningMapEquivSelf ρ).symm v r = r • (v : V) := by
  change (trivialIntertwiningMapEquiv (M := R) ρ).symm _ r = r • (v : V)
  rw [trivialIntertwiningMapEquiv_symm_apply]
  exact ρ.fixedSubmodule.subtype.map_smul r v

/-- An incoming intertwining map from the regular source is determined by its
value at one. -/
theorem trivialIntertwiningMap_apply_eq_smul_one (ρ : Representation R G V)
    (K : IntertwiningMap (Representation.trivial R G R) ρ) (r : R) :
    K r = r • K 1 := by
  have h := congrArg
    (fun F : IntertwiningMap (Representation.trivial R G R) ρ => F r)
    ((trivialIntertwiningMapEquivSelf ρ).symm_apply_apply K)
  simpa only [trivialIntertwiningMapEquivSelf_symm_apply,
    trivialIntertwiningMapEquivSelf_apply] using h.symm

section Naturality

variable {W : Type uW} [AddCommMonoid W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Evaluation at one commutes with a target intertwining map and its map on
fixed submodules. -/
theorem trivialIntertwiningMapEquivSelf_naturality (f : IntertwiningMap ρ σ)
    (K : IntertwiningMap (Representation.trivial R G R) ρ) :
    trivialIntertwiningMapEquivSelf σ (f.comp K) =
      f.fixedSubmoduleMap (trivialIntertwiningMapEquivSelf ρ K) := by
  change trivialIntertwiningMapEquiv (M := R) σ (f.comp K) 1 =
    f.fixedSubmoduleMap (trivialIntertwiningMapEquiv (M := R) ρ K 1)
  simpa only [LinearMap.comp_apply] using
    congrArg (fun F : R →ₗ[R] σ.fixedSubmodule => F 1)
      (trivialIntertwiningMapEquiv_naturality (M := R) f K)

end Naturality

end RegularSource

end Representation
