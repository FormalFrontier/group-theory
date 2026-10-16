/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Torsion in additive quotients

For an additive commutative group `V`, if multiplication by `n` is bijective,
then `(V / L)[n] ≃+ L / nL`. The `n`-torsion group is the kernel of
`nsmulAddMonoidHom n`, and `nL` is the range of that homomorphism on `L`;
no new torsion or quotient carrier is introduced. No topology, lattice,
finiteness, freeness or divisibility at other scalars is needed. There is no
`n ≠ 0` premise: the bijectivity premise permits `n = 0` exactly when `V`
is trivial, and always permits `n = 1`.

For a complex vector space, multiplication by a positive integer is invertible
with inverse multiplication by its reciprocal. Taking an additive lattice `L`
therefore recovers the algebraic identification `n⁻¹L / L ≃+ L / nL` behind
Milne's complex-torus calculation. The lattice's topological and finite-rank
properties are used for further conclusions, not for this identification.

For `n = m * d`, the scalar-transition identity says that the equivalence
intertwines multiplication by `d` on torsion with reduction `L / nL → L / mL`.
It uses the quotient map and the restriction of the scalar map to kernels.
Bijectivity at `n` already implies bijectivity at `m`.

The abstract provider is Mathlib's
`CategoryTheory.ShortComplex.SnakeInput.δIso`, applied to multiplication by `n`
on the short exact sequence `L → V → V / L` in `ModuleCat ℤ`. Every additive
commutative group has its canonical integer-module structure; this introduces
no additional hypothesis on `V` or `L`. Bijectivity makes the middle vertical
kernel and cokernel zero. `CategoryTheory.ShortComplex.SnakeInput.δ_eq` fixes
the positive representative formula `[x] ↦ [n • x]`.

## References

* J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.10, Remark 10.7,
  p. 45, for the complex-torus application.
* Joël Riou, Mathlib's `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean`,
  for the connecting morphism, its characteristic equation, and its
  invertibility when the middle vertical kernel and cokernel vanish.
-/

@[expose] public section

universe u

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) (n : ℕ)
variable (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n))

open CategoryTheory CategoryTheory.Limits

/-- The inclusion/projection row, using the canonical integer modules. -/
private def quotientRow : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom L.subtype.toIntLinearMap)
    (ModuleCat.ofHom (mk' L).toIntLinearMap) (by ext x; simp)

private lemma quotientRow_shortExact : (quotientRow L).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ Subtype.val_injective (mk'_surjective L)
  exact LinearMap.exact_subtype_mkQ L.toIntSubmodule

/-- Multiplication by `n` on the inclusion/projection row. -/
private def nsmulRowMap : quotientRow L ⟶ quotientRow L where
  τ₁ := ModuleCat.ofHom (nsmulAddMonoidHom (α := L) n).toIntLinearMap
  τ₂ := ModuleCat.ofHom (nsmulAddMonoidHom (α := V) n).toIntLinearMap
  τ₃ := ModuleCat.ofHom (nsmulAddMonoidHom (α := V ⧸ L) n).toIntLinearMap
  comm₁₂ := by ext x; rfl
  comm₂₃ := by
    ext x
    exact map_nsmul (mk' L) n x

/-- The snake diagram with categorical vertical kernels and cokernels. -/
private noncomputable def nsmulSnake : ShortComplex.SnakeInput (ModuleCat.{u} ℤ) where
  L₀ := kernel (nsmulRowMap L n)
  L₁ := quotientRow L
  L₂ := quotientRow L
  L₃ := cokernel (nsmulRowMap L n)
  v₀₁ := kernel.ι (nsmulRowMap L n)
  v₁₂ := nsmulRowMap L n
  v₂₃ := cokernel.π (nsmulRowMap L n)
  h₀ := kernelIsKernel _
  h₃ := cokernelIsCokernel _
  L₁_exact := (quotientRow_shortExact L).exact
  epi_L₁_g := (quotientRow_shortExact L).epi_g
  L₂_exact := (quotientRow_shortExact L).exact
  mono_L₂_f := (quotientRow_shortExact L).mono_f

private lemma nsmulSnake_kernel_isZero
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    IsZero (nsmulSnake L n).L₀.X₂ := by
  have : Mono (nsmulSnake L n).v₁₂.τ₂ := (ModuleCat.mono_iff_injective _).mpr hn.1
  exact KernelFork.IsLimit.isZero_of_mono (nsmulSnake L n).h₀τ₂

private lemma nsmulSnake_cokernel_isZero
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    IsZero (nsmulSnake L n).L₃.X₂ := by
  have : Epi (nsmulSnake L n).v₁₂.τ₂ := (ModuleCat.epi_iff_surjective _).mpr hn.2
  exact CokernelCofork.IsColimit.isZero_of_epi (nsmulSnake L n).h₃τ₂

/-- The comparison with the `n`-torsion subgroup. -/
private noncomputable def nsmulKernelIso :
    (nsmulSnake L n).L₀.X₃ ≅
      ModuleCat.of ℤ (nsmulAddMonoidHom (α := V ⧸ L) n).ker :=
  PreservesKernel.iso ShortComplex.π₃ (nsmulRowMap L n) ≪≫
    ModuleCat.kernelIsoKer (nsmulRowMap L n).τ₃

/-- The comparison with the quotient of the subgroup by its `n`-fold multiples. -/
private noncomputable def nsmulCokernelIso :
    (nsmulSnake L n).L₃.X₁ ≅
      ModuleCat.of ℤ (L ⧸ (nsmulAddMonoidHom (α := L) n).range) :=
  PreservesCokernel.iso ShortComplex.π₁ (nsmulRowMap L n) ≪≫
    ModuleCat.cokernelIsoRangeQuotient (nsmulRowMap L n).τ₁

-- The comparison isos involve chosen limits; their canonical instances must unfold here.
set_option backward.isDefEq.respectTransparency false in
private lemma nsmulKernelIso_inv_ι :
    (nsmulKernelIso L n).inv ≫ (nsmulSnake L n).v₀₁.τ₃ =
      ModuleCat.ofHom (nsmulAddMonoidHom (α := V ⧸ L) n).ker.subtype.toIntLinearMap := by
  simp only [nsmulKernelIso, Iso.trans_inv, Category.assoc]
  change (ModuleCat.kernelIsoKer (nsmulRowMap L n).τ₃).inv ≫
    (PreservesKernel.iso ShortComplex.π₃ (nsmulRowMap L n)).inv ≫
      ShortComplex.π₃.map (kernel.ι (nsmulRowMap L n)) = _
  rw [PreservesKernel.iso_inv_ι]
  exact ModuleCat.kernelIsoKer_inv_kernel_ι (nsmulRowMap L n).τ₃

-- Likewise for the chosen colimits in the cokernel comparison.
set_option backward.isDefEq.respectTransparency false in
private lemma nsmulCokernelIso_π_hom :
    (nsmulSnake L n).v₂₃.τ₁ ≫ (nsmulCokernelIso L n).hom =
      ModuleCat.ofHom (mk' (nsmulAddMonoidHom (α := L) n).range).toIntLinearMap := by
  simp only [nsmulCokernelIso, Iso.trans_hom, ← Category.assoc]
  change (ShortComplex.π₁.map (cokernel.π (nsmulRowMap L n)) ≫
    (PreservesCokernel.iso ShortComplex.π₁ (nsmulRowMap L n)).hom) ≫
      (ModuleCat.cokernelIsoRangeQuotient (nsmulRowMap L n).τ₁).hom = _
  rw [PreservesCokernel.π_iso_hom]
  exact ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (nsmulRowMap L n).τ₁

/-- The `n`-torsion of `V / L` is canonically `L / nL` when multiplication by
`n` is bijective on `V`. On representatives the equivalence sends `[x]`
to `[n • x]`, and its inverse sends `[l]` to the class of the unique
`n`-division of `l` in `V`. This is the additive quotient identification used
in Milne, *Abelian Varieties*, I.10, Remark 10.7. -/
@[no_expose] noncomputable def nsmulTorsionEquivQuotient
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    (nsmulAddMonoidHom (α := V ⧸ L) n).ker ≃+
      L ⧸ (nsmulAddMonoidHom (α := L) n).range := by
  exact ((nsmulKernelIso L n).symm ≪≫
    (nsmulSnake L n).δIso (nsmulSnake_kernel_isZero L n hn)
      (nsmulSnake_cokernel_isZero L n hn) ≪≫
    nsmulCokernelIso L n).toLinearEquiv.toAddEquiv

set_option backward.isDefEq.respectTransparency false in
/-- A torsion class represented by `x` maps to the class of `n • x` in `L / nL`. -/
@[simp] theorem nsmulTorsionEquivQuotient_apply_mk (x : V) (hx : n • x ∈ L) :
    nsmulTorsionEquivQuotient L n hn
        ⟨(x : V ⧸ L), by simpa using (eq_zero_iff (n • x)).mpr hx⟩ =
      (⟨n • x, hx⟩ : L) := by
  let t : (nsmulAddMonoidHom (α := V ⧸ L) n).ker :=
    ⟨(x : V ⧸ L), by simpa using (eq_zero_iff (n • x)).mpr hx⟩
  -- Points are tested by maps from the free integer module on one generator.
  -- The lift keeps this test object in the same universe as the diagram.
  let point {M : ModuleCat.{u} ℤ} (m : M) : ModuleCat.of ℤ (ULift.{u} ℤ) ⟶ M :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ M m).comp ULift.moduleEquiv.toLinearMap)
  have h₂ : point x ≫ (nsmulSnake L n).L₁.g =
      (point t ≫ (nsmulKernelIso L n).inv) ≫ (nsmulSnake L n).v₀₁.τ₃ := by
    rw [Category.assoc, nsmulKernelIso_inv_ι]
    ext a
    change ((a.down • x : V) : V ⧸ L) = a.down • (x : V ⧸ L)
    exact map_zsmul (mk' L) a.down x
  have h₁ : point (⟨n • x, hx⟩ : L) ≫ (nsmulSnake L n).L₂.f =
      point x ≫ (nsmulSnake L n).v₁₂.τ₂ := by
    ext a
    change a.down • (n • x) = n • (a.down • x)
    exact smul_comm a.down n x
  have h := (nsmulSnake L n).δ_eq _ _ _ h₂ h₁
  have h' := congrArg (fun f => f ≫ (nsmulCokernelIso L n).hom) h
  simp only [Category.assoc] at h'
  rw [nsmulCokernelIso_π_hom] at h'
  have hval := ConcreteCategory.congr_hom h' (ULift.up (1 : ℤ))
  change (nsmulCokernelIso L n).hom
    ((nsmulSnake L n).δ ((nsmulKernelIso L n).inv t)) =
      (mk' (nsmulAddMonoidHom (α := L) n).range) ⟨n • x, hx⟩
  simpa [point] using! hval

/-- The inverse sends `[l]` to its unique `n`-division class in `V / L`. -/
@[simp] theorem nsmulTorsionEquivQuotient_symm_apply_mk (l : L) :
    ((nsmulTorsionEquivQuotient L n hn).symm
      (l : L ⧸ (nsmulAddMonoidHom (α := L) n).range) : V ⧸ L) =
        ((AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).symm
          (l : V) : V) := by
  let x := (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).symm (l : V)
  have hx : n • x = (l : V) :=
    (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).apply_symm_apply _
  have hxL : n • x ∈ L := hx ▸ l.property
  have hl : (⟨n • x, hxL⟩ : L) = l := Subtype.ext hx
  have h := nsmulTorsionEquivQuotient_apply_mk L n hn x hxL
  rw [hl] at h
  have h' := congrArg (nsmulTorsionEquivQuotient L n hn).symm h
  simpa using congrArg
    (fun y : (nsmulAddMonoidHom (α := V ⧸ L) n).ker => (y : V ⧸ L)) h'.symm

end QuotientAddGroup

namespace AddMonoidHom

variable {A : Type u}

/-- Bijectivity of a product scalar implies bijectivity of its first factor. -/
theorem nsmul_bijective_of_mul [AddCommMonoid A] (m d : ℕ)
    (hmd : Function.Bijective (nsmulAddMonoidHom (α := A) (m * d))) :
    Function.Bijective (nsmulAddMonoidHom (α := A) m) := by
  constructor
  · intro a b hab
    apply hmd.1
    change (m * d) • a = (m * d) • b
    simpa only [mul_nsmul, nsmulAddMonoidHom_apply] using congrArg (fun x : A => d • x) hab
  · intro y
    obtain ⟨x, hx⟩ := hmd.2 y
    exact ⟨d • x, by simpa only [nsmulAddMonoidHom_apply, mul_nsmul'] using hx⟩

/-- Multiples of a product scalar are multiples of its first factor. -/
theorem range_nsmul_mul_le [AddCommGroup A] (m d : ℕ) :
    (nsmulAddMonoidHom (α := A) (m * d)).range ≤
      (nsmulAddMonoidHom (α := A) m).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨d • x, (mul_nsmul' x m d).symm⟩

/-- Multiplication by `d` takes `(m * d)`-torsion to `m`-torsion. -/
theorem nsmul_mapsTo_ker [AddCommGroup A] (m d : ℕ) :
    Set.MapsTo (nsmulAddMonoidHom (α := A) d)
      (nsmulAddMonoidHom (α := A) (m * d)).ker
      (nsmulAddMonoidHom (α := A) m).ker := by
  intro x hx
  change (m * d) • x = 0 at hx
  change m • (d • x) = 0
  simpa only [mul_nsmul'] using hx

end AddMonoidHom

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V]

/-- The quotient-torsion equivalences commute with scalar-divisibility transitions.
For `n = m * d`, multiplication by `d` on `(V / L)[n]` corresponds to
reduction `L / nL → L / mL`. Only bijectivity at `n` is assumed; bijectivity
at `m` follows from the commuting scalar factors. The two arrows below are
`QuotientAddGroup.map` and `AddMonoidHom.restrict` on their usual carriers.
No positivity hypothesis is needed: a zero product forces `V` to be trivial. -/
theorem nsmulTorsionEquivQuotient_naturality (L : AddSubgroup V) (m d : ℕ)
    (hmd : Function.Bijective (nsmulAddMonoidHom (α := V) (m * d))) :
    let reduction : (L ⧸ (nsmulAddMonoidHom (α := L) (m * d)).range) →+
        L ⧸ (nsmulAddMonoidHom (α := L) m).range :=
      map _ _ (AddMonoidHom.id L) (by
        simpa only [AddSubgroup.comap_id] using
          AddMonoidHom.range_nsmul_mul_le (A := L) m d)
    let torsionMap : (nsmulAddMonoidHom (α := V ⧸ L) (m * d)).ker →+
        (nsmulAddMonoidHom (α := V ⧸ L) m).ker :=
      AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker m d)
    reduction.comp (nsmulTorsionEquivQuotient L (m * d) hmd).toAddMonoidHom =
      (nsmulTorsionEquivQuotient L m
        (AddMonoidHom.nsmul_bijective_of_mul m d hmd)).toAddMonoidHom.comp torsionMap := by
  dsimp only
  apply AddMonoidHom.ext
  intro x
  obtain ⟨v, hv⟩ := mk'_surjective L (x : V ⧸ L)
  have hmem : (m * d) • v ∈ L := by
    apply (eq_zero_iff _).mp
    rw [mk_nsmul]
    exact (congrArg (fun q : V ⧸ L => (m * d) • q) hv).trans x.property
  have hx : x = ⟨(v : V ⧸ L), by
      simpa using (eq_zero_iff ((m * d) • v)).mpr hmem⟩ := Subtype.ext hv.symm
  subst x
  have hdmem : m • (d • v) ∈ L := by
    simpa only [mul_nsmul'] using hmem
  have hrestrict : AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker m d)
      ⟨(v : V ⧸ L), by simpa using (eq_zero_iff ((m * d) • v)).mpr hmem⟩ =
      ⟨((d • v : V) : V ⧸ L), by
        simpa using (eq_zero_iff (m • (d • v))).mpr hdmem⟩ :=
    Subtype.ext (mk_nsmul L v d).symm
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hrestrict]
  rw [nsmulTorsionEquivQuotient_apply_mk L (m * d) hmd v hmem,
    nsmulTorsionEquivQuotient_apply_mk L m
      (AddMonoidHom.nsmul_bijective_of_mul m d hmd) (d • v) hdmem, map_mk]
  apply congrArg (fun l : L => (l : L ⧸ (nsmulAddMonoidHom (α := L) m).range))
  apply Subtype.ext
  exact mul_nsmul' v m d

end QuotientAddGroup
