/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Category.Grp.Pushout
public import GroupTheory.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exact short complexes of groups

A short complex in `GrpCat` is exact precisely when the image of the canonical
lift of its first morphism normally generates the categorical kernel of its
second morphism. Normal generation is taken inside this kernel, and the criterion
applies to arbitrary groups.

Normal generation constructs compatible left and right homology data with zero
homology objects. The left cycles are the categorical kernel; any homomorphism
annihilating the lift has normal kernel containing its image, so it is zero.
The right opcycles are the quotient by the normal closure of the image of the
first map; its cokernel universal property is obtained from
`GrpCat.isPushout_quotient_normalClosure`. Normal generation inside the kernel
identifies this ambient normal closure with the kernel of the second map, so the
descended homomorphism is injective and the two homology data are compatible.
Conversely, the normal-closure quotient of the kernel descends through any zero
left homology object, giving normal generation.

An ordinarily exact pair satisfies the criterion: neither injectivity of the
first map nor surjectivity of the second map is required. If the lift image is
normal inside the kernel, normal generation gives surjectivity, and categorical
and multiplicative exactness agree.

## References

* Mathlib's compatible-homology-data framework and definition of exact short
  complexes, formalized by Joël Riou following a suggestion of Adam Topaz, provide
  the categorical notion of exactness.
* The quotient pushout and `QuotientGroup.liftNormalClosureRange` API in
  `GroupTheory.Category.Grp.Pushout` provide the cokernel and its descent, using
  Mathlib's normal-closure formalization by Kexing Ying and quotient-group
  formalization by Kevin Buzzard and Patrick Massot.
* Mathlib's bundled groups, formalized by Johan Commelin, and their epimorphism
  characterization, formalized by Jujian Zhang, relate categorical cancellation
  to surjectivity and injectivity of group homomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace GrpCat

private theorem shortComplex_comp_eq_one (S : ShortComplex GrpCat.{u}) :
    S.g.hom.comp S.f.hom = 1 := by
  simpa only [hom_comp, zero_hom] using congrArg Hom.hom S.zero

private theorem range_kernel_ι_eq_ker {G H : GrpCat.{u}} (f : G ⟶ H) :
    (kernel.ι f).hom.range = f.hom.ker := by
  apply le_antisymm
  · rintro b ⟨x, rfl⟩
    apply MonoidHom.mem_ker.mpr
    have hx := ConcreteCategory.congr_hom (kernel.condition f) x
    simpa only [GrpCat.comp_apply, GrpCat.zero_apply] using hx
  · intro b hb
    let K : GrpCat.{u} := of f.hom.ker
    let i : K ⟶ G := ofHom (Subgroup.subtype f.hom.ker)
    have hi : i ≫ f = 0 := by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro x
      have hx : f.hom (f.hom.ker.subtype x) = 1 :=
        (congrArg f.hom (Subgroup.subtype_apply (s := f.hom.ker) x)).trans
          (MonoidHom.mem_ker.mp x.property)
      simpa only [GrpCat.hom_comp, GrpCat.zero_hom, i, GrpCat.hom_ofHom,
        MonoidHom.comp_apply, MonoidHom.one_apply] using hx
    let j : K ⟶ kernel f := kernel.lift f i hi
    refine ⟨j ⟨b, hb⟩, ?_⟩
    exact ConcreteCategory.congr_hom (kernel.lift_ι f i hi) ⟨b, hb⟩

private theorem normalClosure_range_eq_ker (S : ShortComplex GrpCat.{u})
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    Subgroup.normalClosure (Set.range S.f.hom) = S.g.hom.ker := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨a, rfl⟩
    exact DFunLike.congr_fun (shortComplex_comp_eq_one S) a
  · let N := Subgroup.normalClosure (Set.range S.f.hom)
    have hN : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) ≤
        N.comap (kernel.ι S.g).hom := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨a, rfl⟩
      change kernel.ι S.g (kernel.lift S.g S.f S.zero a) ∈ N
      have ha : kernel.ι S.g (kernel.lift S.g S.f S.zero a) = S.f a :=
        ConcreteCategory.congr_hom (kernel.lift_ι S.g S.f S.zero) a
      rw [ha]
      exact Subgroup.subset_normalClosure ⟨a, rfl⟩
    rw [hgen] at hN
    intro b hb
    rw [← range_kernel_ι_eq_ker S.g] at hb
    obtain ⟨x, rfl⟩ := hb
    exact hN (by simp)

private theorem epi_kernelLift (S : ShortComplex GrpCat.{u})
    (h : Function.MulExact S.f S.g) : Epi (kernel.lift S.g S.f S.zero) := by
  apply (GrpCat.epi_iff_surjective _).2
  intro x
  have hx : S.g (kernel.ι S.g x) = 1 := by
    have hx := ConcreteCategory.congr_hom (kernel.condition S.g) x
    simpa only [GrpCat.comp_apply, GrpCat.zero_apply] using hx
  obtain ⟨a, ha⟩ := (h (kernel.ι S.g x)).1 hx
  refine ⟨a, (GrpCat.mono_iff_injective (kernel.ι S.g)).1 inferInstance ?_⟩
  calc
    kernel.ι S.g (kernel.lift S.g S.f S.zero a) = S.f a :=
      ConcreteCategory.congr_hom (kernel.lift_ι S.g S.f S.zero) a
    _ = kernel.ι S.g x := ha

private lemma quotient_condition (S : ShortComplex GrpCat.{u}) :
    S.f ≫ ofHom (QuotientGroup.mk'
      (Subgroup.normalClosure (Set.range S.f.hom))) = 0 := by
  simpa only [zero_comp] using
    (isPushout_quotient_normalClosure S.f
      (0 : S.X₁ ⟶ (of PUnit : GrpCat.{u}))).w

private noncomputable def quotientIsCokernel (S : ShortComplex GrpCat.{u}) :
    IsColimit (CokernelCofork.ofπ
      (ofHom (QuotientGroup.mk' (Subgroup.normalClosure (Set.range S.f.hom))))
      (quotient_condition S)) := by
  let Q : GrpCat.{u} := of (S.X₂ ⧸ Subgroup.normalClosure (Set.range S.f.hom))
  let p : S.X₂ ⟶ Q := ofHom (QuotientGroup.mk'
    (Subgroup.normalClosure (Set.range S.f.hom)))
  let T : GrpCat.{u} := of PUnit
  have hq : IsPushout S.f (0 : S.X₁ ⟶ T) p (0 : T ⟶ Q) :=
    isPushout_quotient_normalClosure S.f (0 : S.X₁ ⟶ T)
  refine CokernelCofork.IsColimit.ofπ p (quotient_condition S)
    (fun {D} k hk ↦ hq.desc k 0 (by simpa only [zero_comp] using hk))
    (fun {D} k hk ↦ hq.inl_desc k 0 (by simpa only [zero_comp] using hk)) ?_
  intro D k hk m hm
  apply hq.hom_ext
  · exact hm.trans (hq.inl_desc k 0 (by simpa only [zero_comp] using hk)).symm
  · simp only [zero_comp]

/-- The morphism induced on the quotient agrees with quotient-group descent. -/
private theorem quotientIsCokernel_desc (S : ShortComplex GrpCat.{u}) :
    (quotientIsCokernel S).desc (CokernelCofork.ofπ S.g S.zero) =
      ofHom (QuotientGroup.liftNormalClosureRange S.f.hom S.g.hom
        (shortComplex_comp_eq_one S)) := by
  apply hom_ext
  exact QuotientGroup.liftNormalClosureRange_unique S.f.hom S.g.hom
    (shortComplex_comp_eq_one S)
    (congrArg Hom.hom ((quotientIsCokernel S).fac
      (CokernelCofork.ofπ S.g S.zero) WalkingParallelPair.one))

private theorem mono_quotientDesc (S : ShortComplex GrpCat.{u})
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    Mono ((quotientIsCokernel S).desc (CokernelCofork.ofπ S.g S.zero)) := by
  rw [quotientIsCokernel_desc]
  apply (mono_iff_injective _).2
  have hn := normalClosure_range_eq_ker S hgen
  exact (QuotientGroup.injective_lift_iff _ S.g.hom hn.le).2 hn

private def leftHomologyDataOfNormalGeneration (S : ShortComplex GrpCat.{u})
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    S.LeftHomologyData where
  K := kernel S.g
  H := of PUnit
  i := kernel.ι S.g
  π := 0
  wi := kernel.condition S.g
  hi := kernelIsKernel S.g
  wπ := by simp
  hπ := by
    have hlift :
        (kernelIsKernel S.g).lift (KernelFork.ofι S.f S.zero) =
          kernel.lift S.g S.f S.zero := by
      apply (cancel_mono (kernel.ι S.g)).1
      exact ((kernelIsKernel S.g).fac
        (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero).trans
          (kernel.lift_ι S.g S.f S.zero).symm
    refine CokernelCofork.IsColimit.ofπ 0 (by simp)
      (fun {D} k hk ↦ 0) ?_ ?_
    · intro D k hk
      rw [zero_comp]
      symm
      have hker :
          Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) ≤
            k.hom.ker := by
        apply Subgroup.normalClosure_le_normal
        rintro _ ⟨a, rfl⟩
        apply MonoidHom.mem_ker.mpr
        have ha := DFunLike.congr_fun (congrArg Hom.hom hk) a
        rw [hlift] at ha
        simpa only [GrpCat.hom_comp, GrpCat.zero_hom, MonoidHom.comp_apply,
          MonoidHom.one_apply] using ha
      rw [hgen] at hker
      apply GrpCat.ext
      intro x
      rw [GrpCat.zero_apply]
      exact hker (by simp)
    · intro D k hk m hm
      exact (isZero_of_subsingleton (of PUnit : GrpCat.{u})).eq_of_src _ _

private def rightHomologyDataOfNormalGeneration (S : ShortComplex GrpCat.{u})
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    S.RightHomologyData where
  Q := of (S.X₂ ⧸ Subgroup.normalClosure (Set.range S.f.hom))
  H := of PUnit
  p := ofHom (QuotientGroup.mk' (Subgroup.normalClosure (Set.range S.f.hom)))
  ι := 0
  wp := quotient_condition S
  hp := quotientIsCokernel S
  wι := by simp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (mono_quotientDesc S hgen)
    (isZero_of_subsingleton (of PUnit : GrpCat.{u}))

private def homologyDataOfNormalGeneration (S : ShortComplex GrpCat.{u})
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    S.HomologyData := by
  refine
    { left := leftHomologyDataOfNormalGeneration S hgen
      right := rightHomologyDataOfNormalGeneration S hgen
      iso := Iso.refl (of PUnit)
      comm := ?_ }
  change (0 : kernel S.g ⟶ of PUnit) ≫ (𝟙 _) ≫ 0 =
    kernel.ι S.g ≫ ofHom (QuotientGroup.mk'
      (Subgroup.normalClosure (Set.range S.f.hom)))
  rw [zero_comp]
  symm
  apply GrpCat.ext
  intro x
  rw [GrpCat.comp_apply, GrpCat.zero_apply]
  apply (QuotientGroup.eq_one_iff _).2
  rw [normalClosure_range_eq_ker S hgen]
  exact (range_kernel_ι_eq_ker S.g).le ⟨x, rfl⟩

private theorem mulExact_of_surjective_kernel_lift (S : ShortComplex GrpCat.{u})
    (hsurj : Function.Surjective (kernel.lift S.g S.f S.zero).hom) :
    Function.MulExact S.f S.g := by
  apply MonoidHom.mulExact_of_comp_eq_one_of_ker_le_range
    (f := S.f.hom) (g := S.g.hom) (shortComplex_comp_eq_one S)
  intro b hb
  rw [← range_kernel_ι_eq_ker S.g] at hb
  obtain ⟨x, hx⟩ := hb
  obtain ⟨a, ha⟩ := hsurj x
  refine ⟨a, ?_⟩
  calc
    S.f a = kernel.ι S.g (kernel.lift S.g S.f S.zero a) :=
      (ConcreteCategory.congr_hom (kernel.lift_ι S.g S.f S.zero) a).symm
    _ = kernel.ι S.g x := congrArg (kernel.ι S.g) ha
    _ = b := hx

private theorem mulExact_of_normalClosure_range_kernel_lift_eq_top
    (S : ShortComplex GrpCat.{u})
    (hN : ((kernel.lift S.g S.f S.zero).hom.range).Normal)
    (hgen : Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤) :
    Function.MulExact S.f S.g := by
  let : ((kernel.lift S.g S.f S.zero).hom.range).Normal := hN
  apply mulExact_of_surjective_kernel_lift S
  apply MonoidHom.range_eq_top.1
  simpa only [← MonoidHom.coe_range, Subgroup.normalClosure_eq_self] using hgen

/-- An ordinarily exact pair of group homomorphisms is exact as a short complex
of groups. No injectivity or surjectivity assumption on the two maps is needed. -/
theorem exact_of_mulExact (S : ShortComplex GrpCat.{u})
    (h : Function.MulExact S.f S.g) : S.Exact := by
  have hrange : (kernel.lift S.g S.f S.zero).hom.range = ⊤ :=
    MonoidHom.range_eq_top.2 ((GrpCat.epi_iff_surjective _).1 (epi_kernelLift S h))
  have hgen :
      Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤ := by
    rw [← MonoidHom.coe_range, hrange, Subgroup.normalClosure_eq_self]
  refine ⟨⟨homologyDataOfNormalGeneration S hgen, ?_⟩⟩
  exact isZero_of_subsingleton (of PUnit : GrpCat.{u})

/-- A short complex of groups is exact if the range of its first homomorphism
equals the kernel of its second homomorphism. -/
theorem exact_of_range_eq_ker (S : ShortComplex GrpCat.{u})
    (h : S.f.hom.range = S.g.hom.ker) : S.Exact := by
  apply exact_of_mulExact S
  exact (MonoidHom.mulExact_iff (f := S.f.hom) (g := S.g.hom)).2 h.symm

/-- In an exact short complex of groups, the canonical lift of the first morphism
normally generates the kernel of the second morphism. -/
theorem normalClosure_range_kernel_lift_eq_top_of_exact
    (S : ShortComplex GrpCat.{u}) (h : S.Exact) :
    Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤ := by
  obtain ⟨hd, hzero⟩ := h.condition
  let L := hd.left
  let e := IsLimit.conePointUniqueUpToIso L.hi (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = L.i := by
    simpa using
      (IsLimit.conePointUniqueUpToIso_hom_comp L.hi (kernelIsKernel S.g)
        WalkingParallelPair.zero)
  have hf : L.f' ≫ e.hom = kernel.lift S.g S.f S.zero := by
    apply (cancel_mono (kernel.ι S.g)).1
    rw [Category.assoc, he, L.f'_i, kernel.lift_ι]
  let N := Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom)
  let Q : GrpCat.{u} := of ((kernel S.g : GrpCat.{u}) ⧸ N)
  let q : kernel S.g ⟶ Q := ofHom (QuotientGroup.mk' N)
  have hq : kernel.lift S.g S.f S.zero ≫ q = 0 := by
    apply GrpCat.ext
    intro x
    rw [GrpCat.comp_apply, GrpCat.zero_apply]
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  have hL : L.f' ≫ (e.hom ≫ q) = 0 := by
    rw [← Category.assoc, hf, hq]
  have heq : e.hom ≫ q = 0 := by
    calc
      e.hom ≫ q = L.π ≫ L.descH (e.hom ≫ q) hL :=
        (L.π_descH (e.hom ≫ q) hL).symm
      _ = 0 := by
        rw [hzero.eq_zero_of_src (L.descH (e.hom ≫ q) hL), comp_zero]
  have hqzero : q = 0 := by
    apply (cancel_epi e.hom).1
    simpa only [comp_zero] using heq
  change N = ⊤
  apply top_unique
  intro x _
  apply (QuotientGroup.eq_one_iff x).1
  have hqhom : QuotientGroup.mk' N = 1 := by
    simpa only [q, GrpCat.hom_ofHom, GrpCat.zero_hom] using congrArg Hom.hom hqzero
  simpa only [QuotientGroup.mk'_apply, MonoidHom.one_apply] using
    DFunLike.congr_fun hqhom x

/-- A short complex of arbitrary groups is exact precisely when the image of its
canonical kernel lift normally generates the kernel of its second morphism. -/
theorem exact_iff_normalClosure_range_kernel_lift_eq_top (S : ShortComplex GrpCat.{u}) :
    S.Exact ↔
      Subgroup.normalClosure (Set.range (kernel.lift S.g S.f S.zero).hom) = ⊤ := by
  constructor
  · exact normalClosure_range_kernel_lift_eq_top_of_exact S
  · intro hgen
    refine ⟨⟨homologyDataOfNormalGeneration S hgen, ?_⟩⟩
    exact isZero_of_subsingleton (of PUnit : GrpCat.{u})

/-- Categorical and multiplicative exactness agree if the image of the canonical
kernel lift is normal inside the kernel. -/
theorem exact_iff_mulExact_of_normal_range_kernel_lift
    (S : ShortComplex GrpCat.{u})
    (hN : ((kernel.lift S.g S.f S.zero).hom.range).Normal) :
    S.Exact ↔ Function.MulExact S.f S.g := by
  constructor
  · intro h
    exact mulExact_of_normalClosure_range_kernel_lift_eq_top S hN
      (normalClosure_range_kernel_lift_eq_top_of_exact S h)
  · exact exact_of_mulExact S

end GrpCat
