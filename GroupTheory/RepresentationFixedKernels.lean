/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.LinearAlgebra.ComapSubtype
public import GroupTheory.RepresentationFixedUniversalProperty

/-!
# Fixed vectors in kernels and equalizers

For an intertwining map `f`, the pullback of the fixed submodule to the ambient
kernel is linearly equivalent to the kernel of `f.fixedSubmoduleMap`. Parallel
intertwining maps give the analogous equivalence for their equalizer. Both
comparisons preserve the underlying vector, in both directions, and commute
with the inclusions into the ambient module. They are natural in commutative
squares of intertwining maps, by naturality of the submodule equivalences on
the two inclusions of the common intersection.

The comparisons transport the ordinary kernel and equalizer factorizations of
linear maps into the fixed submodule. The source of such a linear map needs no
representation. Only a semiring, a monoid and modules with commutative monoid
addition are required; the equalizer is defined without subtraction. For an
incoming intertwining map from a trivial representation, vanishing of its
composite with `f` characterizes the unique ambient kernel factorization.

The constructions use Mathlib's submodule equivalences through the common
intersection and its `LinearMap.codRestrict` factorization. Their sources are
explicit comaps of submodules, not fixed submodules of restricted
representations.
-/

@[expose] public section

set_option autoImplicit false

universe uR uG uV uW uX uV' uW'

namespace Representation.IntertwiningMap

variable {R : Type uR} [Semiring R]

variable {G : Type uG} {V : Type uV} {W : Type uW} [Monoid G]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- The equalizer of the maps on fixed vectors is the pullback of the ambient
equalizer along the fixed-submodule inclusion. -/
theorem eqLocus_fixedSubmoduleMap (f h : IntertwiningMap ρ σ) :
    LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap =
      (LinearMap.eqLocus f.toLinearMap h.toLinearMap).comap ρ.fixedSubmodule.subtype := by
  ext x
  simp only [LinearMap.mem_eqLocus, Submodule.mem_comap]
  constructor
  · intro hx
    simpa using congrArg (fun y : σ.fixedSubmodule => (y : W)) hx
  · intro hx
    apply Subtype.ext
    simpa using hx

/-- Fixed vectors lying in the ambient kernel correspond linearly to the kernel
of the induced map on fixed submodules, with the same ambient values. -/
noncomputable def fixedSubmoduleKerEquiv (f : IntertwiningMap ρ σ) :
    ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype ≃ₗ[R]
      LinearMap.ker f.fixedSubmoduleMap := by
  let F := ρ.fixedSubmodule
  let K := LinearMap.ker f.toLinearMap
  let eK : F.comap K.subtype ≃ₗ[R] (F ⊓ K : Submodule R V) :=
    (LinearEquiv.ofEq (F.comap K.subtype) ((F ⊓ K).comap K.subtype) (by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)).trans
      (Submodule.comapSubtypeEquivOfLe (show F ⊓ K ≤ K from inf_le_right))
  let eF : K.comap F.subtype ≃ₗ[R] (F ⊓ K : Submodule R V) :=
    (LinearEquiv.ofEq (K.comap F.subtype) ((F ⊓ K).comap F.subtype) (by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)).trans
      (Submodule.comapSubtypeEquivOfLe (show F ⊓ K ≤ F from inf_le_left))
  exact (eK.trans eF.symm).trans (LinearEquiv.ofEq _ _ f.ker_fixedSubmoduleMap.symm)

/-- The kernel comparison preserves the underlying ambient vector. -/
@[simp]
theorem fixedSubmoduleKerEquiv_apply_val (f : IntertwiningMap ρ σ)
    (x : ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype) :
    ((f.fixedSubmoduleKerEquiv x).val : V) = (x.val : V) := by
  rfl

/-- The inverse kernel comparison preserves the underlying ambient vector. -/
@[simp]
theorem fixedSubmoduleKerEquiv_symm_apply_val (f : IntertwiningMap ρ σ)
    (x : LinearMap.ker f.fixedSubmoduleMap) :
    (((f.fixedSubmoduleKerEquiv).symm x).val : V) = (x.val : V) := by
  rfl

/-- The kernel comparison commutes with the linear inclusions into the ambient
module. -/
theorem subtype_comp_fixedSubmoduleKerEquiv (f : IntertwiningMap ρ σ) :
    (ρ.fixedSubmodule.subtype.comp (LinearMap.ker f.fixedSubmoduleMap).subtype).comp
        f.fixedSubmoduleKerEquiv.toLinearMap =
      (LinearMap.ker f.toLinearMap).subtype.comp
        (ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype).subtype := by
  apply LinearMap.ext
  intro x
  exact f.fixedSubmoduleKerEquiv_apply_val x

/-- Fixed vectors lying in the ambient equalizer correspond linearly to the
equalizer of the induced maps on fixed submodules, with the same ambient values. -/
noncomputable def fixedSubmoduleEqLocusEquiv (f h : IntertwiningMap ρ σ) :
    ρ.fixedSubmodule.comap (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype ≃ₗ[R]
      LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap := by
  let F := ρ.fixedSubmodule
  let E := LinearMap.eqLocus f.toLinearMap h.toLinearMap
  let eE : F.comap E.subtype ≃ₗ[R] (F ⊓ E : Submodule R V) :=
    (LinearEquiv.ofEq (F.comap E.subtype) ((F ⊓ E).comap E.subtype) (by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)).trans
      (Submodule.comapSubtypeEquivOfLe (show F ⊓ E ≤ E from inf_le_right))
  let eF : E.comap F.subtype ≃ₗ[R] (F ⊓ E : Submodule R V) :=
    (LinearEquiv.ofEq (E.comap F.subtype) ((F ⊓ E).comap F.subtype) (by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)).trans
      (Submodule.comapSubtypeEquivOfLe (show F ⊓ E ≤ F from inf_le_left))
  exact (eE.trans eF.symm).trans
    (LinearEquiv.ofEq _ _ (f.eqLocus_fixedSubmoduleMap h).symm)

/-- The equalizer comparison preserves the underlying ambient vector. -/
@[simp]
theorem fixedSubmoduleEqLocusEquiv_apply_val (f h : IntertwiningMap ρ σ)
    (x : ρ.fixedSubmodule.comap (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype) :
    ((f.fixedSubmoduleEqLocusEquiv h x).val : V) = (x.val : V) := by
  rfl

/-- The inverse equalizer comparison preserves the underlying ambient vector. -/
@[simp]
theorem fixedSubmoduleEqLocusEquiv_symm_apply_val (f h : IntertwiningMap ρ σ)
    (x : LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap) :
    (((f.fixedSubmoduleEqLocusEquiv h).symm x).val : V) = (x.val : V) := by
  rfl

/-- The equalizer comparison commutes with the linear inclusions into the
ambient module. -/
theorem subtype_comp_fixedSubmoduleEqLocusEquiv (f h : IntertwiningMap ρ σ) :
    (ρ.fixedSubmodule.subtype.comp
        (LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap).subtype).comp
        (f.fixedSubmoduleEqLocusEquiv h).toLinearMap =
      (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype.comp
        (ρ.fixedSubmodule.comap
          (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype).subtype := by
  apply LinearMap.ext
  intro x
  exact f.fixedSubmoduleEqLocusEquiv_apply_val h x

section Lifts

variable {X : Type uX} [AddCommMonoid X] [Module R X]

/-- A linear map into the fixed submodule is killed by the induced map exactly
when it factors uniquely through fixed vectors in the ambient kernel. The
factorization equation is an equality of maps into the ambient module. -/
theorem existsUnique_fixedSubmoduleKerLift_iff (f : IntertwiningMap ρ σ)
    (t : X →ₗ[R] ρ.fixedSubmodule) :
    f.fixedSubmoduleMap.comp t = 0 ↔
      ∃! l : X →ₗ[R] ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype,
        ((LinearMap.ker f.toLinearMap).subtype.comp
          (ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype).subtype).comp l =
            ρ.fixedSubmodule.subtype.comp t := by
  constructor
  · intro ht
    have ht_mem : ∀ x, t x ∈ LinearMap.ker f.fixedSubmoduleMap := by
      intro x
      exact LinearMap.mem_ker.mpr (DFunLike.congr_fun ht x)
    let k := LinearMap.codRestrict (LinearMap.ker f.fixedSubmoduleMap) t ht_mem
    have hk : (LinearMap.ker f.fixedSubmoduleMap).subtype.comp k = t :=
      LinearMap.subtype_comp_codRestrict (f := t) _ ht_mem
    let l := (f.fixedSubmoduleKerEquiv).symm.toLinearMap.comp k
    have hl :
        ((LinearMap.ker f.toLinearMap).subtype.comp
          (ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype).subtype).comp l =
            ρ.fixedSubmodule.subtype.comp t := by
      apply LinearMap.ext
      intro x
      calc
        ((l x).val : V) = ((k x).val : V) :=
          f.fixedSubmoduleKerEquiv_symm_apply_val (k x)
        _ = (t x : V) :=
          congrArg (fun y : ρ.fixedSubmodule => (y : V)) (DFunLike.congr_fun hk x)
    refine ⟨l, hl, ?_⟩
    intro m hm
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (DFunLike.congr_fun hm x).trans (DFunLike.congr_fun hl x).symm
  · rintro ⟨l, hl, _⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : f.toLinearMap ((l x).val : V) = 0 :=
      LinearMap.mem_ker.mp (l x).val.property
    have hval : ((l x).val : V) = (t x : V) := DFunLike.congr_fun hl x
    simpa using hval ▸ hx

/-- A linear map into the fixed submodule equalizes the induced maps exactly
when it factors uniquely through fixed vectors in their ambient equalizer. The
factorization equation is an equality of maps into the ambient module. -/
theorem existsUnique_fixedSubmoduleEqLocusLift_iff (f h : IntertwiningMap ρ σ)
    (t : X →ₗ[R] ρ.fixedSubmodule) :
    f.fixedSubmoduleMap.comp t = h.fixedSubmoduleMap.comp t ↔
      ∃! l : X →ₗ[R]
          ρ.fixedSubmodule.comap (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype,
        ((LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype.comp
          (ρ.fixedSubmodule.comap
            (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype).subtype).comp l =
              ρ.fixedSubmodule.subtype.comp t := by
  constructor
  · intro ht
    have ht_mem : ∀ x, t x ∈ LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap := by
      intro x
      exact LinearMap.mem_eqLocus.mpr (DFunLike.congr_fun ht x)
    let k := LinearMap.codRestrict
      (LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap) t ht_mem
    have hk :
        (LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap).subtype.comp k = t :=
      LinearMap.subtype_comp_codRestrict (f := t) _ ht_mem
    let l := (f.fixedSubmoduleEqLocusEquiv h).symm.toLinearMap.comp k
    have hl :
        ((LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype.comp
          (ρ.fixedSubmodule.comap
            (LinearMap.eqLocus f.toLinearMap h.toLinearMap).subtype).subtype).comp l =
              ρ.fixedSubmodule.subtype.comp t := by
      apply LinearMap.ext
      intro x
      calc
        ((l x).val : V) = ((k x).val : V) :=
          f.fixedSubmoduleEqLocusEquiv_symm_apply_val h (k x)
        _ = (t x : V) :=
          congrArg (fun y : ρ.fixedSubmodule => (y : V)) (DFunLike.congr_fun hk x)
    refine ⟨l, hl, ?_⟩
    intro m hm
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (DFunLike.congr_fun hm x).trans (DFunLike.congr_fun hl x).symm
  · rintro ⟨l, hl, _⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : f.toLinearMap ((l x).val : V) = h.toLinearMap ((l x).val : V) :=
      LinearMap.mem_eqLocus.mp (l x).val.property
    have hval : ((l x).val : V) = (t x : V) := DFunLike.congr_fun hl x
    simpa using hval ▸ hx

/-- An intertwining map from a trivial representation is killed by `f` exactly
when its underlying linear map factors uniquely through fixed vectors in the
ambient kernel of `f`. -/
theorem existsUnique_trivialIntertwiningMapKerLift_iff (f : IntertwiningMap ρ σ)
    (K : IntertwiningMap (Representation.trivial R G X) ρ) :
    f.comp K = 0 ↔
      ∃! l : X →ₗ[R] ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype,
        ((LinearMap.ker f.toLinearMap).subtype.comp
          (ρ.fixedSubmodule.comap (LinearMap.ker f.toLinearMap).subtype).subtype).comp l =
            K.toLinearMap := by
  have hzero :
      f.comp K = 0 ↔
        f.fixedSubmoduleMap.comp (Representation.trivialIntertwiningMapEquiv ρ K) = 0 := by
    rw [← Representation.trivialIntertwiningMapEquiv_naturality f K]
    constructor
    · intro hK
      rw [hK]
      exact (Representation.trivialIntertwiningMapEquiv (M := X) σ).map_zero
    · intro hK
      apply (Representation.trivialIntertwiningMapEquiv (M := X) σ).injective
      exact hK.trans
        (Representation.trivialIntertwiningMapEquiv (M := X) σ).map_zero.symm
  rw [hzero,
    f.existsUnique_fixedSubmoduleKerLift_iff
      (Representation.trivialIntertwiningMapEquiv ρ K),
    Representation.subtype_comp_trivialIntertwiningMapEquiv ρ K]

end Lifts

section Naturality

variable {V' : Type uV'} {W' : Type uW'}
variable [AddCommMonoid V'] [Module R V'] [AddCommMonoid W'] [Module R W']
variable {ρ' : Representation R G V'} {σ' : Representation R G W'}

/-- The kernel comparison is natural in a commutative square of intertwining
maps. Both maps between kernels are restrictions of the given map `a`; their
membership proofs follow from the square and the map on fixed submodules. -/
theorem fixedSubmoduleKerEquiv_naturality
    (f : IntertwiningMap ρ σ) (f' : IntertwiningMap ρ' σ')
    (a : IntertwiningMap ρ ρ') (b : IntertwiningMap σ σ')
    (sq : f'.comp a = b.comp f) :
    let F := ρ.fixedSubmodule
    let F' := ρ'.fixedSubmodule
    let K := LinearMap.ker f.toLinearMap
    let K' := LinearMap.ker f'.toLinearMap
    let uK : K →ₗ[R] K' :=
      LinearMap.codRestrict K' (a.toLinearMap.comp K.subtype) (by
        intro x
        apply LinearMap.mem_ker.mpr
        have hx : f (x : V) = 0 := LinearMap.mem_ker.mp x.property
        simpa [comp_apply, hx] using
          congrArg (fun k : IntertwiningMap ρ σ' => k (x : V)) sq)
    let sourceMap : F.comap K.subtype →ₗ[R] F'.comap K'.subtype :=
      LinearMap.codRestrict (F'.comap K'.subtype)
        (uK.comp (F.comap K.subtype).subtype) (by
          intro x
          simpa [F', uK, Submodule.mem_comap] using
            (a.fixedSubmoduleMap ⟨(x.val : V), x.property⟩).property)
    let targetMap : LinearMap.ker f.fixedSubmoduleMap →ₗ[R]
        LinearMap.ker f'.fixedSubmoduleMap :=
      LinearMap.codRestrict (LinearMap.ker f'.fixedSubmoduleMap)
        (a.fixedSubmoduleMap.comp (LinearMap.ker f.fixedSubmoduleMap).subtype) (by
          intro x
          have hx : (x.val : V) ∈ K := by
            simpa only [f.ker_fixedSubmoduleMap, Submodule.mem_comap,
              Submodule.subtype_apply] using x.property
          have hy := (uK ⟨(x.val : V), hx⟩).property
          rw [f'.ker_fixedSubmoduleMap]
          simpa [K', uK, Submodule.mem_comap] using hy)
    f'.fixedSubmoduleKerEquiv.toLinearMap.comp sourceMap =
      targetMap.comp f.fixedSubmoduleKerEquiv.toLinearMap := by
  intro F F' K K' uK sourceMap targetMap
  let I : Submodule R V := F ⊓ K
  let I' : Submodule R V' := F' ⊓ K'
  let iK : I ≤ K := inf_le_right
  let iK' : I' ≤ K' := inf_le_right
  let iF : I ≤ F := inf_le_left
  let iF' : I' ≤ F' := inf_le_left
  let vI : I →ₗ[R] I' :=
    LinearMap.codRestrict I' (a.toLinearMap.comp I.subtype) (by
      intro x
      constructor
      · simpa [F'] using
          (a.fixedSubmoduleMap ⟨(x : V), x.property.1⟩).property
      · simpa [uK] using (uK ⟨(x : V), x.property.2⟩).property)
  have squareK :
      uK.comp (LinearMap.codRestrict K I.subtype (fun x => iK x.property)) =
        (LinearMap.codRestrict K' I'.subtype (fun x => iK' x.property)).comp vI := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  have squareF :
      a.fixedSubmoduleMap.comp
          (LinearMap.codRestrict F I.subtype (fun x => iF x.property)) =
        (LinearMap.codRestrict F' I'.subtype (fun x => iF' x.property)).comp vI := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact a.fixedSubmoduleMap_apply ⟨(x : V), iF x.property⟩
  have hK := Submodule.comapSubtypeEquivOfLe_naturality iK iK' uK vI squareK
  have hF := Submodule.comapSubtypeEquivOfLe_naturality
    iF iF' a.fixedSubmoduleMap vI squareF
  let cK : F.comap K.subtype ≃ₗ[R] I.comap K.subtype :=
    LinearEquiv.ofEq _ _ (by
      ext x
      simp only [Submodule.mem_comap, I, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)
  let cK' : F'.comap K'.subtype ≃ₗ[R] I'.comap K'.subtype :=
    LinearEquiv.ofEq _ _ (by
      ext x
      simp only [Submodule.mem_comap, I', Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)
  let cF : LinearMap.ker f.fixedSubmoduleMap ≃ₗ[R] I.comap F.subtype :=
    LinearEquiv.ofEq _ _ (by
      rw [f.ker_fixedSubmoduleMap]
      ext x
      simp only [Submodule.mem_comap, I, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)
  let cF' : LinearMap.ker f'.fixedSubmoduleMap ≃ₗ[R] I'.comap F'.subtype :=
    LinearEquiv.ofEq _ _ (by
      rw [f'.ker_fixedSubmoduleMap]
      ext x
      simp only [Submodule.mem_comap, I', Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)
  let eK := cK.trans (Submodule.comapSubtypeEquivOfLe iK)
  let eK' := cK'.trans (Submodule.comapSubtypeEquivOfLe iK')
  let eF := cF.trans (Submodule.comapSubtypeEquivOfLe iF)
  let eF' := cF'.trans (Submodule.comapSubtypeEquivOfLe iF')
  have he (x : F.comap K.subtype) :
      eF (f.fixedSubmoduleKerEquiv x) = eK x := by
    apply Subtype.ext
    exact f.fixedSubmoduleKerEquiv_apply_val x
  have he' (x : F'.comap K'.subtype) :
      eF' (f'.fixedSubmoduleKerEquiv x) = eK' x := by
    apply Subtype.ext
    exact f'.fixedSubmoduleKerEquiv_apply_val x
  apply LinearMap.ext
  intro x
  apply eF'.injective
  calc
    eF' (f'.fixedSubmoduleKerEquiv (sourceMap x)) = eK' (sourceMap x) := he' _
    _ = vI (eK x) := DFunLike.congr_fun hK (cK x)
    _ = vI (eF (f.fixedSubmoduleKerEquiv x)) := congrArg vI (he x).symm
    _ = eF' (targetMap (f.fixedSubmoduleKerEquiv x)) := by
      symm
      exact DFunLike.congr_fun hF (cF (f.fixedSubmoduleKerEquiv x))

/-- The equalizer comparison is natural in two commutative squares with the
same vertical intertwining maps. The induced maps on both equalizers retain
the given map `a` on underlying ambient vectors. -/
theorem fixedSubmoduleEqLocusEquiv_naturality
    (f h : IntertwiningMap ρ σ) (f' h' : IntertwiningMap ρ' σ')
    (a : IntertwiningMap ρ ρ') (b : IntertwiningMap σ σ')
    (sqf : f'.comp a = b.comp f) (sqh : h'.comp a = b.comp h) :
    let F := ρ.fixedSubmodule
    let F' := ρ'.fixedSubmodule
    let E := LinearMap.eqLocus f.toLinearMap h.toLinearMap
    let E' := LinearMap.eqLocus f'.toLinearMap h'.toLinearMap
    let uE : E →ₗ[R] E' :=
      LinearMap.codRestrict E' (a.toLinearMap.comp E.subtype) (by
        intro x
        apply LinearMap.mem_eqLocus.mpr
        calc
          f' (a (x : V)) = b (f (x : V)) := by
            simpa using congrArg (fun k : IntertwiningMap ρ σ' => k (x : V)) sqf
          _ = b (h (x : V)) := congrArg b (LinearMap.mem_eqLocus.mp x.property)
          _ = h' (a (x : V)) := by
            symm
            simpa using congrArg (fun k : IntertwiningMap ρ σ' => k (x : V)) sqh)
    let sourceMap : F.comap E.subtype →ₗ[R] F'.comap E'.subtype :=
      LinearMap.codRestrict (F'.comap E'.subtype)
        (uE.comp (F.comap E.subtype).subtype) (by
          intro x
          simpa [F', uE, Submodule.mem_comap] using
            (a.fixedSubmoduleMap ⟨(x.val : V), x.property⟩).property)
    let targetMap : LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap →ₗ[R]
        LinearMap.eqLocus f'.fixedSubmoduleMap h'.fixedSubmoduleMap :=
      LinearMap.codRestrict
        (LinearMap.eqLocus f'.fixedSubmoduleMap h'.fixedSubmoduleMap)
        (a.fixedSubmoduleMap.comp
          (LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap).subtype) (by
          intro x
          have hx : (x.val : V) ∈ E := by
            simpa only [f.eqLocus_fixedSubmoduleMap h, Submodule.mem_comap,
              Submodule.subtype_apply] using x.property
          have hy := (uE ⟨(x.val : V), hx⟩).property
          rw [f'.eqLocus_fixedSubmoduleMap h']
          simpa [E', uE, Submodule.mem_comap] using hy)
    (f'.fixedSubmoduleEqLocusEquiv h').toLinearMap.comp sourceMap =
      targetMap.comp (f.fixedSubmoduleEqLocusEquiv h).toLinearMap := by
  intro F F' E E' uE sourceMap targetMap
  let I : Submodule R V := F ⊓ E
  let I' : Submodule R V' := F' ⊓ E'
  let iE : I ≤ E := inf_le_right
  let iE' : I' ≤ E' := inf_le_right
  let iF : I ≤ F := inf_le_left
  let iF' : I' ≤ F' := inf_le_left
  let vI : I →ₗ[R] I' :=
    LinearMap.codRestrict I' (a.toLinearMap.comp I.subtype) (by
      intro x
      constructor
      · simpa [F'] using
          (a.fixedSubmoduleMap ⟨(x : V), x.property.1⟩).property
      · simpa [uE] using (uE ⟨(x : V), x.property.2⟩).property)
  have squareE :
      uE.comp (LinearMap.codRestrict E I.subtype (fun x => iE x.property)) =
        (LinearMap.codRestrict E' I'.subtype (fun x => iE' x.property)).comp vI := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  have squareF :
      a.fixedSubmoduleMap.comp
          (LinearMap.codRestrict F I.subtype (fun x => iF x.property)) =
        (LinearMap.codRestrict F' I'.subtype (fun x => iF' x.property)).comp vI := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact a.fixedSubmoduleMap_apply ⟨(x : V), iF x.property⟩
  have hE := Submodule.comapSubtypeEquivOfLe_naturality iE iE' uE vI squareE
  have hF := Submodule.comapSubtypeEquivOfLe_naturality
    iF iF' a.fixedSubmoduleMap vI squareF
  let cE : F.comap E.subtype ≃ₗ[R] I.comap E.subtype :=
    LinearEquiv.ofEq _ _ (by
      ext x
      simp only [Submodule.mem_comap, I, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)
  let cE' : F'.comap E'.subtype ≃ₗ[R] I'.comap E'.subtype :=
    LinearEquiv.ofEq _ _ (by
      ext x
      simp only [Submodule.mem_comap, I', Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨hx, x.property⟩, fun hx => hx.1⟩)
  let cF : LinearMap.eqLocus f.fixedSubmoduleMap h.fixedSubmoduleMap ≃ₗ[R]
      I.comap F.subtype :=
    LinearEquiv.ofEq _ _ (by
      rw [f.eqLocus_fixedSubmoduleMap h]
      ext x
      simp only [Submodule.mem_comap, I, Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)
  let cF' : LinearMap.eqLocus f'.fixedSubmoduleMap h'.fixedSubmoduleMap ≃ₗ[R]
      I'.comap F'.subtype :=
    LinearEquiv.ofEq _ _ (by
      rw [f'.eqLocus_fixedSubmoduleMap h']
      ext x
      simp only [Submodule.mem_comap, I', Submodule.mem_inf, Submodule.subtype_apply]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩)
  let eE := cE.trans (Submodule.comapSubtypeEquivOfLe iE)
  let eE' := cE'.trans (Submodule.comapSubtypeEquivOfLe iE')
  let eF := cF.trans (Submodule.comapSubtypeEquivOfLe iF)
  let eF' := cF'.trans (Submodule.comapSubtypeEquivOfLe iF')
  have he (x : F.comap E.subtype) :
      eF (f.fixedSubmoduleEqLocusEquiv h x) = eE x := by
    apply Subtype.ext
    exact f.fixedSubmoduleEqLocusEquiv_apply_val h x
  have he' (x : F'.comap E'.subtype) :
      eF' (f'.fixedSubmoduleEqLocusEquiv h' x) = eE' x := by
    apply Subtype.ext
    exact f'.fixedSubmoduleEqLocusEquiv_apply_val h' x
  apply LinearMap.ext
  intro x
  apply eF'.injective
  calc
    eF' (f'.fixedSubmoduleEqLocusEquiv h' (sourceMap x)) = eE' (sourceMap x) := he' _
    _ = vI (eE x) := DFunLike.congr_fun hE (cE x)
    _ = vI (eF (f.fixedSubmoduleEqLocusEquiv h x)) := congrArg vI (he x).symm
    _ = eF' (targetMap (f.fixedSubmoduleEqLocusEquiv h x)) := by
      symm
      exact DFunLike.congr_fun hF (cF (f.fixedSubmoduleEqLocusEquiv h x))

end Naturality

end Representation.IntertwiningMap
