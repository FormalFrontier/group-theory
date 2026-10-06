/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CharacterSubgroups
public import GroupTheory.Topology.CircleCharacter
public import GroupTheory.Topology.RationalCircle
public import GroupTheory.Topology.TypeTags
public import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Rational-circle and continuous circle characters

Composition with the canonical rational-circle inclusion sends open-kernel
characters to continuous circle characters. For compact nonarchimedean
commutative additive groups this map is an additive equivalence. If such a group
is additionally Hausdorff and has a dense finitely generated additive subgroup,
the finite-order character subgroup supplies the same domain.

The comparison concerns open-kernel characters, not arbitrary abstract
rational-circle characters. Its target is the underlying additive group of
the Pontryagin dual, without an assertion about transported topologies.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1.
* The rational-circle inclusion and finite-order preimages follow the
  formalization in Supernatural Numbers.
-/

@[expose] public section

open scoped Topology

universe u v

namespace CharacterModule

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A]

section Forward

variable [IsTopologicalAddGroup A]

/-- The continuous circle character obtained from an open-kernel rational-circle character. -/
noncomputable def openKernelToPontryagin :
    openKernel A →+ Additive (PontryaginDual (Multiplicative A)) where
  toFun c := Additive.ofMul {
    toFun := fun a => Additive.toMul (AddCircle.rationalToCircle (c.1 a.toAdd))
    map_one' := by
      change Additive.toMul (AddCircle.rationalToCircle (c.1 0)) = 1
      simp
    map_mul' := by
      intro a b
      change Additive.toMul (AddCircle.rationalToCircle (c.1 (a.toAdd + b.toAdd))) =
        Additive.toMul (AddCircle.rationalToCircle (c.1 a.toAdd)) *
          Additive.toMul (AddCircle.rationalToCircle (c.1 b.toAdd))
      simp
    continuous_toFun := by
      have hlc : IsLocallyConstant
          (fun a : Multiplicative A => (c.1 : CharacterModule A) a.toAdd) :=
        (isLocallyConstant_of_mem_openKernel c.property).comp_continuous
          continuous_toAdd
      exact (hlc.comp (fun q => Additive.toMul (AddCircle.rationalToCircle q))).continuous
  }
  map_zero' := by
    apply PontryaginDual.ext
    intro a
    change Additive.toMul (AddCircle.rationalToCircle (0 : AddCircle (1 : ℚ))) = 1
    simp
  map_add' := by
    intro c d
    apply PontryaginDual.ext
    intro a
    change Additive.toMul (AddCircle.rationalToCircle (c.1 a.toAdd + d.1 a.toAdd)) =
      Additive.toMul (AddCircle.rationalToCircle (c.1 a.toAdd)) *
        Additive.toMul (AddCircle.rationalToCircle (d.1 a.toAdd))
    rw [map_add, toMul_add]

/-- Evaluation of the canonical continuous character is evaluation through
the rational-circle inclusion. -/
@[simp] theorem openKernelToPontryagin_apply (c : openKernel A) (a : A) :
    Additive.toMul (openKernelToPontryagin c) (Multiplicative.ofAdd a) =
      Additive.toMul (AddCircle.rationalToCircle (c.1 a)) := rfl

/-- Distinct open-kernel rational-circle characters yield distinct circle characters. -/
theorem openKernelToPontryagin_injective :
    Function.Injective (openKernelToPontryagin (A := A)) := by
  intro c d h
  apply Subtype.ext
  apply CharacterModule.ext
  intro a
  apply AddCircle.rationalToCircle_injective
  have heval := congrArg
    (fun χ : Additive (PontryaginDual (Multiplicative A)) =>
      Additive.toMul χ (Multiplicative.ofAdd a)) h
  simpa only [openKernelToPontryagin_apply, ofMul_toMul] using
    congrArg Additive.ofMul heval

/-- The forward construction commutes with continuous precomposition and
`PontryaginDual.map`. -/
theorem openKernelToPontryagin_naturality {B : Type v} [AddCommGroup B]
    [TopologicalSpace B] [IsTopologicalAddGroup B]
    (f : A →ₜ+ B) (c : openKernel B) :
    openKernelToPontryagin (openKernelRestrict f c) =
      Additive.ofMul (PontryaginDual.map f.toMultiplicative
        (Additive.toMul (openKernelToPontryagin c))) := by
  apply PontryaginDual.ext
  intro a
  rfl

end Forward

omit [TopologicalSpace A] in
private theorem coe_eq_of_subgroup_eq {S T : AddSubgroup (CharacterModule A)}
    (h : S = T) (c : T) : ((h.symm ▸ c : S) : CharacterModule A) = c.1 := by
  cases h
  rfl

omit [TopologicalSpace A] in
private theorem subgroup_equiv_transport_apply {S T : AddSubgroup (CharacterModule A)}
    {B : Type*} [AddGroup B] (h : S = T) (e : S ≃+ B) (c : T) :
    (h ▸ e) c = e (h.symm ▸ c) := by
  cases h
  rfl

section Comparison

variable [CompactSpace A] [NonarchimedeanAddGroup A]

/-- Every continuous circle character on a compact nonarchimedean commutative
additive group comes from an open-kernel rational-circle character. -/
theorem openKernelToPontryagin_surjective :
    Function.Surjective (openKernelToPontryagin (A := A)) := by
  intro χ
  let ψ : PontryaginDual (Multiplicative A) := Additive.toMul χ
  have hfinite : (Set.range ψ).Finite := Circle.finite_range ψ
  have horder (a : A) : IsOfFinOrder (ψ (Multiplicative.ofAdd a)) := by
    apply (finite_powers).mp
    apply hfinite.subset
    intro z hz
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hz
    exact ⟨(Multiplicative.ofAdd a) ^ n, map_pow ψ _ n⟩
  choose q hq using fun a : A =>
    Circle.exists_rational_preimage_of_isOfFinOrder (horder a)
  let c : CharacterModule A := {
    toFun := q
    map_zero' := by
      apply AddCircle.rationalToCircle_injective
      have hzero : Additive.toMul (AddCircle.rationalToCircle (q (0 : A))) =
          Additive.toMul (AddCircle.rationalToCircle (0 : AddCircle (1 : ℚ))) := by
        simpa using hq (0 : A)
      simpa only [ofMul_toMul] using congrArg Additive.ofMul hzero
    map_add' := by
      intro a b
      apply AddCircle.rationalToCircle_injective
      have hadd : Additive.toMul (AddCircle.rationalToCircle (q (a + b))) =
          Additive.toMul (AddCircle.rationalToCircle (q a + q b)) := by
        rw [map_add, toMul_add, hq (a + b), hq a, hq b]
        exact map_mul ψ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      simpa only [ofMul_toMul] using congrArg Additive.ofMul hadd
  }
  have hker : (c.ker : Set A) =
      (fun a : A => Multiplicative.ofAdd a) ⁻¹'
        (ψ.toMonoidHom.ker : Set (Multiplicative A)) := by
    ext a
    change c a = 0 ↔ ψ (Multiplicative.ofAdd a) = 1
    rw [← hq a]
    constructor
    · intro ha
      change q a = 0 at ha
      simp [ha]
    · intro ha
      change q a = 0
      apply AddCircle.rationalToCircle_injective
      have hzero : Additive.toMul (AddCircle.rationalToCircle (q a)) =
          Additive.toMul (AddCircle.rationalToCircle (0 : AddCircle (1 : ℚ))) := by
        simpa using ha
      simpa only [ofMul_toMul] using congrArg Additive.ofMul hzero
  have hc : c ∈ openKernel A := by
    apply (mem_openKernel c).mpr
    rw [hker]
    exact (Circle.isOpen_ker ψ).preimage continuous_ofAdd
  refine ⟨⟨c, hc⟩, ?_⟩
  apply PontryaginDual.ext
  intro a
  change Additive.toMul (AddCircle.rationalToCircle (q a.toAdd)) = ψ a
  exact hq a.toAdd

/-- Open-kernel rational-circle characters identify additively with
continuous circle-valued characters. -/
noncomputable def openKernelEquivPontryagin :
    openKernel A ≃+ Additive (PontryaginDual (Multiplicative A)) :=
  AddEquiv.ofBijective openKernelToPontryagin
    ⟨openKernelToPontryagin_injective, openKernelToPontryagin_surjective⟩

/-- The equivalence evaluates through the canonical rational-circle inclusion. -/
@[simp] theorem openKernelEquivPontryagin_apply (c : openKernel A) (a : A) :
    Additive.toMul (openKernelEquivPontryagin (A := A) c)
        (Multiplicative.ofAdd a) =
      Additive.toMul (AddCircle.rationalToCircle (c.1 a)) := by
  rfl

/-- Pointwise evaluation characterizes the rational-circle inverse. -/
theorem openKernelEquivPontryagin_symm_apply
    (χ : Additive (PontryaginDual (Multiplicative A))) (a : A) :
    Additive.toMul (AddCircle.rationalToCircle
      (((openKernelEquivPontryagin (A := A)).symm χ).1 a)) =
      Additive.toMul χ (Multiplicative.ofAdd a) := by
  rw [← openKernelEquivPontryagin_apply,
    (openKernelEquivPontryagin (A := A)).apply_symm_apply]

/-- A character with the prescribed pointwise circle values is the unique inverse. -/
theorem openKernelEquivPontryagin_symm_eq_iff
    (c : openKernel A) (χ : Additive (PontryaginDual (Multiplicative A))) :
    (openKernelEquivPontryagin (A := A)).symm χ = c ↔
      ∀ a : A, Additive.toMul (AddCircle.rationalToCircle (c.1 a)) =
        Additive.toMul χ (Multiplicative.ofAdd a) := by
  constructor
  · intro h a
    rw [← h]
    exact openKernelEquivPontryagin_symm_apply χ a
  · intro h
    apply (openKernelEquivPontryagin (A := A)).injective
    apply PontryaginDual.ext
    intro a
    rw [(openKernelEquivPontryagin (A := A)).apply_symm_apply]
    change Additive.toMul χ (Multiplicative.ofAdd a.toAdd) =
      Additive.toMul (AddCircle.rationalToCircle (c.1 a.toAdd))
    exact (h a.toAdd).symm

/-- The equivalence commutes with continuous restriction of open-kernel
characters and with contravariant restriction of Pontryagin duals. -/
theorem openKernelEquivPontryagin_naturality {B : Type v} [AddCommGroup B]
    [TopologicalSpace B] [CompactSpace B]
    [NonarchimedeanAddGroup B] (f : A →ₜ+ B) (c : openKernel B) :
    openKernelEquivPontryagin (A := A) (openKernelRestrict f c) =
      Additive.ofMul (PontryaginDual.map f.toMultiplicative
        (Additive.toMul (openKernelEquivPontryagin (A := B) c))) := by
  exact openKernelToPontryagin_naturality f c

/-- The inverse comparison also commutes with continuous restriction. -/
theorem openKernelEquivPontryagin_symm_naturality {B : Type v} [AddCommGroup B]
    [TopologicalSpace B] [CompactSpace B]
    [NonarchimedeanAddGroup B] (f : A →ₜ+ B)
    (χ : Additive (PontryaginDual (Multiplicative B))) :
    openKernelRestrict f ((openKernelEquivPontryagin (A := B)).symm χ) =
      (openKernelEquivPontryagin (A := A)).symm
        (Additive.ofMul (PontryaginDual.map f.toMultiplicative
          (Additive.toMul χ))) := by
  apply (openKernelEquivPontryagin (A := A)).injective
  rw [openKernelEquivPontryagin_naturality,
    (openKernelEquivPontryagin (A := B)).apply_symm_apply,
    (openKernelEquivPontryagin (A := A)).apply_symm_apply]

variable [T2Space A]

/-- Finite-order rational-circle characters of a compact nonarchimedean
commutative additive group that is additionally Hausdorff and has a dense
finitely generated additive subgroup identify with its continuous
circle-valued characters. -/
noncomputable def torsionEquivPontryaginOfDenseFG (D : AddSubgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A)) :
    AddCommGroup.torsion (CharacterModule A) ≃+
      Additive (PontryaginDual (Multiplicative A)) :=
  (openKernel_eq_torsion_of_dense_fg D hfg hdense) ▸ openKernelEquivPontryagin

/-- Evaluation of the finite-order comparison uses the same canonical inclusion. -/
@[simp] theorem torsionEquivPontryaginOfDenseFG_apply (D : AddSubgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A))
    (c : AddCommGroup.torsion (CharacterModule A)) (a : A) :
    Additive.toMul (torsionEquivPontryaginOfDenseFG D hfg hdense c)
        (Multiplicative.ofAdd a) =
      Additive.toMul (AddCircle.rationalToCircle (c.1 a)) := by
  rw [torsionEquivPontryaginOfDenseFG, subgroup_equiv_transport_apply,
    openKernelEquivPontryagin_apply,
    coe_eq_of_subgroup_eq (openKernel_eq_torsion_of_dense_fg D hfg hdense) c]

/-- Finite-order comparison commutes with algebraic character restriction and
the contravariant continuous Pontryagin dual map. -/
theorem torsionEquivPontryaginOfDenseFG_naturality {B : Type v}
    [AddCommGroup B] [TopologicalSpace B]
    [CompactSpace B] [NonarchimedeanAddGroup B] [T2Space B]
    (D : AddSubgroup A) (hfg : D.FG) (hdense : Dense (D : Set A))
    (E : AddSubgroup B) (hfgE : E.FG) (hdenseE : Dense (E : Set B))
    (f : A →ₜ+ B) (c : AddCommGroup.torsion (CharacterModule B)) :
    torsionEquivPontryaginOfDenseFG D hfg hdense
        (torsionRestrict f.toAddMonoidHom c) =
      Additive.ofMul (PontryaginDual.map f.toMultiplicative
        (Additive.toMul (torsionEquivPontryaginOfDenseFG E hfgE hdenseE c))) := by
  apply PontryaginDual.ext
  intro a
  change Additive.toMul (torsionEquivPontryaginOfDenseFG D hfg hdense
      (torsionRestrict f.toAddMonoidHom c)) (Multiplicative.ofAdd a.toAdd) =
    Additive.toMul (torsionEquivPontryaginOfDenseFG E hfgE hdenseE c)
      (Multiplicative.ofAdd (f a.toAdd))
  rw [torsionEquivPontryaginOfDenseFG_apply,
    torsionEquivPontryaginOfDenseFG_apply]
  rfl

/-- The inverse finite-order comparison has the prescribed circle-valued evaluations. -/
@[simp] theorem torsionEquivPontryaginOfDenseFG_symm_apply (D : AddSubgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A))
    (χ : Additive (PontryaginDual (Multiplicative A))) (a : A) :
    Additive.toMul (AddCircle.rationalToCircle
      (((torsionEquivPontryaginOfDenseFG D hfg hdense).symm χ).1 a)) =
      Additive.toMul χ (Multiplicative.ofAdd a) := by
  rw [← torsionEquivPontryaginOfDenseFG_apply D hfg hdense,
    (torsionEquivPontryaginOfDenseFG D hfg hdense).apply_symm_apply]

/-- Pointwise circle evaluations characterize the inverse finite-order character. -/
theorem torsionEquivPontryaginOfDenseFG_symm_eq_iff (D : AddSubgroup A)
    (hfg : D.FG) (hdense : Dense (D : Set A))
    (c : AddCommGroup.torsion (CharacterModule A))
    (χ : Additive (PontryaginDual (Multiplicative A))) :
    (torsionEquivPontryaginOfDenseFG D hfg hdense).symm χ = c ↔
      ∀ a : A, Additive.toMul (AddCircle.rationalToCircle (c.1 a)) =
        Additive.toMul χ (Multiplicative.ofAdd a) := by
  constructor
  · intro h a
    rw [← h]
    exact torsionEquivPontryaginOfDenseFG_symm_apply D hfg hdense χ a
  · intro h
    apply (torsionEquivPontryaginOfDenseFG D hfg hdense).injective
    apply PontryaginDual.ext
    intro a
    rw [(torsionEquivPontryaginOfDenseFG D hfg hdense).apply_symm_apply]
    change Additive.toMul χ (Multiplicative.ofAdd a.toAdd) =
      Additive.toMul (torsionEquivPontryaginOfDenseFG D hfg hdense c)
        (Multiplicative.ofAdd a.toAdd)
    rw [torsionEquivPontryaginOfDenseFG_apply D hfg hdense]
    exact (h a.toAdd).symm

/-- The inverse finite-order comparison commutes with continuous precomposition. -/
theorem torsionEquivPontryaginOfDenseFG_symm_naturality {B : Type v}
    [AddCommGroup B] [TopologicalSpace B]
    [CompactSpace B] [NonarchimedeanAddGroup B] [T2Space B]
    (D : AddSubgroup A) (hfg : D.FG) (hdense : Dense (D : Set A))
    (E : AddSubgroup B) (hfgE : E.FG) (hdenseE : Dense (E : Set B))
    (f : A →ₜ+ B) (χ : Additive (PontryaginDual (Multiplicative B))) :
    torsionRestrict f.toAddMonoidHom
        ((torsionEquivPontryaginOfDenseFG E hfgE hdenseE).symm χ) =
      (torsionEquivPontryaginOfDenseFG D hfg hdense).symm
        (Additive.ofMul (PontryaginDual.map f.toMultiplicative (Additive.toMul χ))) := by
  apply (torsionEquivPontryaginOfDenseFG D hfg hdense).injective
  rw [torsionEquivPontryaginOfDenseFG_naturality D hfg hdense E hfgE hdenseE,
    (torsionEquivPontryaginOfDenseFG E hfgE hdenseE).apply_symm_apply,
    (torsionEquivPontryaginOfDenseFG D hfg hdense).apply_symm_apply]

end Comparison

end CharacterModule

end
