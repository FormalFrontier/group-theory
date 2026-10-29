/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.GroupTheory.MonoidLocalization.Lemmas
public import GroupTheory.Semigroup.StableEquality

/-!
# Grothendieck lifts and cofinal kernels

`Algebra.GrothendieckAddGroup.piEquiv` identifies the completion of an arbitrary dependent
product of additive commutative monoids with the product of their completions. Its forward
coordinates are the induced evaluation maps, and it is natural in families of additive
homomorphisms. An induced product map is bijective exactly when every induced coordinate
map is bijective. No finiteness, cancellation or nonempty-index hypothesis is required.

The universal property of the Grothendieck additive group is additive in the supplied
homomorphism. `Algebra.GrothendieckAddGroup.liftAddEquiv` equips Mathlib's equivalence
`Algebra.GrothendieckAddGroup.lift` with this structure, retaining both its forward map and
its inverse, restriction along `Algebra.GrothendieckAddGroup.of`.

`Algebra.GrothendieckAddGroup.lift_injective_iff` characterizes injectivity of a lift by
reflection of stable equality in the source monoid.
`Algebra.GrothendieckAddGroup.lift_of_comp_injective_iff` specializes this criterion to the
homomorphism induced by an additive homomorphism between commutative monoids.
`Algebra.GrothendieckAddGroup.mem_ker_lift_of_comp_iff_of_cofinal` describes the kernel
of this induced homomorphism when every target element can be completed to an image element
by adding a summand. Its kernel elements are precisely differences of source generators
whose images are equal in the original target monoid.

`Algebra.GrothendieckAddGroup.lift₂` extends a curried biadditive map to the Grothendieck
additive groups of both source monoids. Its values on pairs of canonical generators
characterize the extension. The construction uses the pointwise additive groups on
homomorphism spaces; it requires neither cancellation of the source monoids nor
nontriviality of the target group.

## References

* Mathlib's completion and universal-property formalization by Alex J. Best and Yaël Dillies
  in `Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup`.
* Mathlib's localization injectivity criterion
  `AddSubmonoid.LocalizationMap.lift_injective_iff` in
  `Mathlib.GroupTheory.MonoidLocalization.Maps` and equality criterion
  `AddSubmonoid.LocalizationMap.eq_iff_exists` in
  `Mathlib.GroupTheory.MonoidLocalization.Basic`.
* Mathlib's product-localization formalization by Junyan Xu in
  `Mathlib.GroupTheory.MonoidLocalization.Lemmas` and the equivalence
  `AddLocalization.addEquivOfQuotient` in `Mathlib.GroupTheory.MonoidLocalization.Maps`.
* Mathlib's pointwise group structures on homomorphism spaces in
  `Mathlib.Algebra.Group.Hom.Instances` and additive-equivalence constructors in
  `Mathlib.Algebra.Group.Equiv.Defs`.
-/

@[expose] public section

universe u v w u' v' w'

namespace Algebra.GrothendieckAddGroup

/-- Two elements have the same image in the Grothendieck additive group exactly when they
become equal after adding a common summand. -/
theorem of_eq_iff_exists {A : Type u} [AddCommMonoid A] {x y : A} :
    of x = of y ↔ ∃ a : A, x + a = y + a := by
  change (AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)) x =
    (AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)) y ↔ _
  rw [AddSubmonoid.LocalizationMap.eq_iff_exists]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a : A), by simpa only [add_comm] using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, AddSubmonoid.mem_top a⟩, by simpa only [add_comm] using ha⟩

variable {A : Type u} {G : Type w} [AddCommMonoid A] [AddCommGroup G]

/-- The lift agrees with the supplied homomorphism on canonical generators. -/
@[simp]
theorem lift_of (f : A →+ G) (a : A) :
    lift f (AddLocalization.addMonoidOf ⊤ a) = f a := by
  exact DFunLike.congr_fun ((lift (M := A) (G := G)).symm_apply_apply f) a

/-- Homomorphisms out of the Grothendieck additive group are determined by generators. -/
@[ext]
theorem hom_ext {f g : GrothendieckAddGroup A →+ G}
    (h : ∀ a : A, f (of a) = g (of a)) : f = g := by
  apply (lift (M := A) (G := G)).symm.injective
  exact AddMonoidHom.ext h

/-- A homomorphism's lift to the Grothendieck additive group is injective exactly when
equality of its values implies stable equality in the source monoid. -/
theorem lift_injective_iff (g : A →+ G) :
    Function.Injective (lift g) ↔
      ∀ x y : A, g x = g y → ∃ a : A, x + a = y + a := by
  change Function.Injective
    ((AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)).lift
      (g := g) (fun _ ↦ AddGroup.isAddUnit _)) ↔ _
  rw [AddSubmonoid.LocalizationMap.lift_injective_iff]
  constructor
  · intro h x y hxy
    exact of_eq_iff_exists.mp ((h x y).mpr hxy)
  · intro h x y
    constructor
    · exact (AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)).eq_of_eq
        (fun _ ↦ AddGroup.isAddUnit _)
    · intro hxy
      exact of_eq_iff_exists.mpr (h x y hxy)

/-- Grothendieck lifting preserves the pointwise sum of homomorphisms. -/
theorem lift_add (f g : A →+ G) : lift (f + g) = lift f + lift g := by
  apply hom_ext
  intro a
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift_of,
    AddMonoidHom.add_apply]

/-- The additive universal property of the Grothendieck additive group, with restriction
along `of` as its inverse. -/
noncomputable def liftAddEquiv : (A →+ G) ≃+ (GrothendieckAddGroup A →+ G) :=
  AddEquiv.mk' lift lift_add

/-- The underlying equivalence of the additive lift is Mathlib's Grothendieck lift. -/
@[simp]
theorem liftAddEquiv_toEquiv :
    (liftAddEquiv (A := A) (G := G) :
      (A →+ G) ≃ (GrothendieckAddGroup A →+ G)) = lift := rfl

/-- The additive lift has the same forward map as the Grothendieck lift. -/
@[simp]
theorem liftAddEquiv_apply (f : A →+ G) : liftAddEquiv f = lift f := rfl

/-- The inverse additive lift restricts along the canonical map to the completion. -/
@[simp]
theorem liftAddEquiv_symm_apply (f : GrothendieckAddGroup A →+ G) :
    (liftAddEquiv (A := A) (G := G)).symm f = f.comp of := rfl

variable {B : Type v} [AddCommMonoid B]

/-- The induced homomorphism between Grothendieck additive groups is injective exactly when
stable equality of images implies stable equality in the source monoid. -/
theorem lift_of_comp_injective_iff (f : A →+ B) :
    Function.Injective (lift ((of (M := B)).comp f)) ↔
      ∀ x y : A, (∃ t : B, f x + t = f y + t) → ∃ a : A, x + a = y + a := by
  rw [lift_injective_iff]
  simp only [AddMonoidHom.comp_apply, of_eq_iff_exists]

/-- If every target element can be completed to an image element by adding a summand, the
kernel of the induced homomorphism consists exactly of differences of source generators
with equal images in the target monoid. -/
theorem mem_ker_lift_of_comp_iff_of_cofinal (f : A →+ B)
    (hcof : ∀ b : B, ∃ a : A, ∃ c : B, b + c = f a)
    (z : GrothendieckAddGroup A) :
    z ∈ (lift ((of (M := B)).comp f)).ker ↔
      ∃ x y : A, f x = f y ∧ z = of x - of y := by
  constructor
  · intro hz
    obtain ⟨⟨x, y⟩, hxy⟩ :=
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)).surj z
    have hzxy : z = of x - of (y : A) := eq_sub_iff_add_eq.mpr hxy
    have himage : of (f x) = of (f (y : A)) := by
      rw [hzxy, AddMonoidHom.sub_mem_ker_iff] at hz
      simpa only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift_of,
        AddMonoidHom.comp_apply] using hz
    obtain ⟨a, ha⟩ :=
      (AddHomClass.exists_add_right_eq_iff_exists_map_eq f hcof x (y : A)).mp
        (of_eq_iff_exists.mp himage)
    refine ⟨x + a, (y : A) + a, ha, ?_⟩
    simpa only [map_add, add_sub_add_right_eq_sub] using hzxy
  · rintro ⟨x, y, hxy, rfl⟩
    rw [AddMonoidHom.sub_mem_ker_iff]
    simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift_of,
      AddMonoidHom.comp_apply, hxy]

/-- Extend a curried biadditive map to the Grothendieck additive groups of both sources. -/
noncomputable def lift₂ (f : A →+ B →+ G) :
    GrothendieckAddGroup A →+ GrothendieckAddGroup B →+ G :=
  lift ((liftAddEquiv (A := B) (G := G)).toAddMonoidHom.comp f)

/-- On a generator in the first variable, the bilinear extension is the lift in the second. -/
@[simp]
theorem lift₂_of_left (f : A →+ B →+ G) (a : A) :
    lift₂ f (AddLocalization.addMonoidOf ⊤ a) = lift (f a) := by
  exact lift_of ((liftAddEquiv (A := B) (G := G)).toAddMonoidHom.comp f) a

/-- The bilinear extension agrees with the supplied map on pairs of generators. -/
theorem lift₂_of (f : A →+ B →+ G) (a : A) (b : B) :
    lift₂ f (AddLocalization.addMonoidOf ⊤ a) (AddLocalization.addMonoidOf ⊤ b) =
      f a b := by
  rw [lift₂_of_left, lift_of]

/-- On a generator in the second variable, the bilinear extension is the lift in the first. -/
@[simp]
theorem lift₂_of_right (f : A →+ B →+ G) (x : GrothendieckAddGroup A) (b : B) :
    lift₂ f x (AddLocalization.addMonoidOf ⊤ b) = lift (f.flip b) x := by
  have h : (lift₂ f).flip (of b) = lift (f.flip b) := by
    apply hom_ext
    intro a
    simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply,
      AddMonoidHom.flip_apply, lift₂_of, lift_of]
  exact DFunLike.congr_fun h x

/-- Curried biadditive maps on Grothendieck additive groups are determined by pairs of
canonical generators. -/
theorem hom_ext₂ {f g : GrothendieckAddGroup A →+ GrothendieckAddGroup B →+ G}
    (h : ∀ (a : A) (b : B), f (of a) (of b) = g (of a) (of b)) : f = g := by
  apply hom_ext
  intro a
  apply hom_ext
  exact h a

/-- The bilinear extension is the unique curried biadditive map with the prescribed values
on pairs of canonical generators. -/
theorem lift₂_unique (f : A →+ B →+ G)
    (g : GrothendieckAddGroup A →+ GrothendieckAddGroup B →+ G)
    (h : ∀ (a : A) (b : B), g (of a) (of b) = f a b) : lift₂ f = g := by
  apply hom_ext₂
  intro a b
  exact (lift₂_of f a b).trans (h a b).symm

/-- Extending a biadditive map commutes with precomposition in both source monoids. -/
theorem lift₂_comp {A' : Type u'} {B' : Type v'}
    [AddCommMonoid A'] [AddCommMonoid B']
    (f : A →+ B →+ G) (g : A' →+ A) (h : B' →+ B) :
    lift₂ ((f.compl₂ h).comp g) =
      ((lift₂ f).compl₂ (lift (of.comp h))).comp (lift (of.comp g)) := by
  apply hom_ext₂
  intro a b
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift₂_of,
    AddMonoidHom.comp_apply, AddMonoidHom.compl₂_apply, lift_of]

/-- Extending a biadditive map commutes with postcomposition by an additive homomorphism. -/
theorem lift₂_compr₂ {H : Type w'} [AddCommGroup H]
    (f : A →+ B →+ G) (h : G →+ H) :
    lift₂ (f.compr₂ h) = (lift₂ f).compr₂ h := by
  apply hom_ext₂
  intro a b
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift₂_of,
    AddMonoidHom.compr₂_apply]

/-!
## Range and surjectivity of induced homomorphisms

Membership of a canonical generator in the range of an induced homomorphism is equivalent
to expressing it as a difference of image elements after adding a common summand.
Surjectivity is characterized by this condition on all elements of the original target
monoid. Together with reflection of stable equality, it also characterizes bijectivity.
-/

/-- A canonical generator belongs to the range of the induced homomorphism exactly when it
is a difference of image elements after adding a common summand in the target monoid. -/
theorem of_mem_range_lift_of_comp_iff (f : A →+ B) (b : B) :
    of b ∈ Set.range (lift ((of (M := B)).comp f)) ↔
      ∃ a₁ a₂ : A, ∃ t : B, b + f a₂ + t = f a₁ + t := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨⟨a₁, a₂⟩, ha⟩ :=
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid A)).surj q
    have h : of b + of (f a₂) = of (f a₁) := by
      simpa only [map_add, lift_of, AddMonoidHom.comp_apply, hq] using
        congrArg (lift ((of (M := B)).comp f)) ha
    refine ⟨a₁, a₂, of_eq_iff_exists.mp ?_⟩
    simpa only [map_add] using h
  · rintro ⟨a₁, a₂, t, ht⟩
    have h : of (b + f a₂) = of (f a₁) := of_eq_iff_exists.mpr ⟨t, ht⟩
    refine ⟨of a₁ - of a₂, ?_⟩
    simp only [map_sub, AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift_of,
      AddMonoidHom.comp_apply]
    apply sub_eq_iff_eq_add.mpr
    simpa only [map_add, AddSubmonoid.LocalizationMap.toAddMonoidHom_apply] using h.symm

/-- The induced homomorphism is surjective exactly when every element of the original
target monoid is a difference of image elements after adding a common summand. -/
theorem lift_of_comp_surjective_iff (f : A →+ B) :
    Function.Surjective (lift ((of (M := B)).comp f)) ↔
      ∀ b : B, ∃ a₁ a₂ : A, ∃ t : B, b + f a₂ + t = f a₁ + t := by
  constructor
  · intro h b
    exact (of_mem_range_lift_of_comp_iff f b).mp (h (of b))
  · intro h q
    obtain ⟨⟨b₁, b₂⟩, hb⟩ :=
      (AddLocalization.addMonoidOf (⊤ : AddSubmonoid B)).surj q
    obtain ⟨q₁, hq₁⟩ := (of_mem_range_lift_of_comp_iff f b₁).mpr (h b₁)
    obtain ⟨q₂, hq₂⟩ := (of_mem_range_lift_of_comp_iff f b₂).mpr (h b₂)
    refine ⟨q₁ - q₂, ?_⟩
    rw [map_sub, hq₁, hq₂]
    exact sub_eq_iff_eq_add.mpr hb.symm

/-- The induced homomorphism is bijective exactly when it reflects stable equality and
every element of the original target monoid is a stabilized difference of image elements. -/
theorem lift_of_comp_bijective_iff (f : A →+ B) :
    Function.Bijective (lift ((of (M := B)).comp f)) ↔
      (∀ x y : A, (∃ t : B, f x + t = f y + t) → ∃ a : A, x + a = y + a) ∧
      (∀ b : B, ∃ a₁ a₂ : A, ∃ t : B, b + f a₂ + t = f a₁ + t) := by
  rw [Function.Bijective, lift_of_comp_injective_iff, lift_of_comp_surjective_iff]

/-!
## Completion of arbitrary products

The product of the canonical unit maps is a localization at the top additive submonoid:
its denominators are tuples, with no common-denominator or finite-support restriction.
The equivalence below specializes Mathlib's product-localization theorem and quotient
localization equivalence. Its unit law applies to every tuple in the full product.
-/

section Pi

variable {I : Type u} (M : I → Type v) [∀ i, AddCommMonoid (M i)]

/-- The canonical additive equivalence between the completion of a dependent product and
its coordinate completions, induced by the product of the canonical unit maps. -/
noncomputable def piEquiv :
    GrothendieckAddGroup (∀ i, M i) ≃+ ∀ i, GrothendieckAddGroup (M i) :=
  let l : AddSubmonoid.LocalizationMap (⊤ : AddSubmonoid (∀ i, M i))
      (∀ i, GrothendieckAddGroup (M i)) :=
    { toFun := AddMonoidHom.piMap (fun i ↦ of (M := M i))
      map_add' := (AddMonoidHom.piMap (fun i ↦ of (M := M i))).map_add
      isLocalizationMap := by
        have hfun : ⇑(AddMonoidHom.piMap (fun i ↦ of (M := M i))) =
            Pi.map (fun i ↦ of (M := M i)) := by
          funext a i
          exact AddMonoidHom.piMap_apply _ a i
        simpa only [AddSubmonoid.pi_top, ← hfun] using
          (AddSubmonoid.IsLocalizationMap.pi (N := fun i ↦ GrothendieckAddGroup (M i))
            (fun i ↦ (⊤ : AddSubmonoid (M i))) (f := fun i ↦ of (M := M i))
            (fun i ↦ (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (M i))).isLocalizationMap)) }
  AddLocalization.addEquivOfQuotient l

/-- The product equivalence sends every tuple's canonical unit to its coordinate units. -/
@[simp]
theorem piEquiv_of (a : ∀ i, M i) :
    piEquiv M (AddLocalization.addMonoidOf ⊤ a) = fun i ↦ of (a i) := by
  simp only [piEquiv, AddLocalization.addEquivOfQuotient_addMonoidOf]
  funext i
  exact AddMonoidHom.piMap_apply (fun i ↦ of (M := M i)) a i

/-- Each coordinate of the product equivalence is the induced evaluation homomorphism. -/
@[simp]
theorem piEquiv_apply (x : GrothendieckAddGroup (∀ i, M i)) (i : I) :
    piEquiv M x i = lift ((of (M := M i)).comp (Pi.evalAddMonoidHom M i)) x := by
  have h : (Pi.evalAddMonoidHom (fun i ↦ GrothendieckAddGroup (M i)) i).comp
      (piEquiv M).toAddMonoidHom =
        lift ((of (M := M i)).comp (Pi.evalAddMonoidHom M i)) := by
    apply hom_ext
    intro a
    change piEquiv M (of a) i = _
    simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, piEquiv_of, lift_of,
      AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
  exact DFunLike.congr_fun h x

/-- Induced evaluation recovers each coordinate of the inverse product equivalence. -/
@[simp]
theorem lift_eval_piEquiv_symm (z : ∀ i, GrothendieckAddGroup (M i)) (i : I) :
    lift ((of (M := M i)).comp (Pi.evalAddMonoidHom M i)) ((piEquiv M).symm z) = z i := by
  rw [← piEquiv_apply]
  exact congrFun ((piEquiv M).apply_symm_apply z) i

variable {M} {N : I → Type w} [∀ i, AddCommMonoid (N i)]

/-- The product equivalence is natural in a family of additive monoid homomorphisms. -/
theorem piEquiv_natural (f : ∀ i, M i →+ N i) :
    (piEquiv N).toAddMonoidHom.comp
        (lift ((of (M := ∀ i, N i)).comp (AddMonoidHom.piMap f))) =
      (AddMonoidHom.piMap (fun i ↦ lift ((of (M := N i)).comp (f i)))).comp
        (piEquiv M).toAddMonoidHom := by
  apply hom_ext
  intro a
  ext i
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.piMap_apply]
  change piEquiv N (lift ((of (M := ∀ i, N i)).comp (AddMonoidHom.piMap f)) (of a)) i =
    lift ((of (M := N i)).comp (f i)) (piEquiv M (of a) i)
  simp only [AddSubmonoid.LocalizationMap.toAddMonoidHom_apply, lift_of, piEquiv_of,
    AddMonoidHom.comp_apply, AddMonoidHom.piMap_apply]

/-- The induced homomorphism on a product's completion is bijective exactly when every
induced homomorphism on a coordinate completion is bijective. -/
theorem lift_of_comp_piMap_bijective_iff (f : ∀ i, M i →+ N i) :
    Function.Bijective (lift ((of (M := ∀ i, N i)).comp (AddMonoidHom.piMap f))) ↔
      ∀ i, Function.Bijective (lift ((of (M := N i)).comp (f i))) := by
  let F : GrothendieckAddGroup (∀ i, M i) → GrothendieckAddGroup (∀ i, N i) :=
    lift ((of (M := ∀ i, N i)).comp (AddMonoidHom.piMap f))
  let g : ∀ i, GrothendieckAddGroup (M i) → GrothendieckAddGroup (N i) :=
    fun i ↦ lift ((of (M := N i)).comp (f i))
  let eM := (piEquiv M).toEquiv
  let eN := (piEquiv N).toEquiv
  have hnat : eN ∘ F = Pi.map g ∘ eM := by
    funext x i
    change piEquiv N (F x) i = g i (piEquiv M x i)
    have h := congrFun (DFunLike.congr_fun (piEquiv_natural f) x) i
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.piMap_apply] at h
    change piEquiv N (F x) i = g i (piEquiv M x i) at h
    exact h
  have hconj : Pi.map g = eN ∘ F ∘ eM.symm := by
    funext z
    have h := congrFun hnat (eM.symm z)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm
  have hconj' : F = eN.symm ∘ Pi.map g ∘ eM := by
    funext x
    have h := congrArg eN.symm (congrFun hnat x)
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  have hprod : Function.Bijective F ↔ Function.Bijective (Pi.map g) := by
    constructor
    · intro hF
      rw [hconj]
      exact eN.bijective.comp (hF.comp eM.symm.bijective)
    · intro hg
      rw [hconj']
      exact eN.symm.bijective.comp (hg.comp eM.bijective)
  refine hprod.trans ?_
  constructor
  · intro hg i
    refine ⟨(Pi.map_injective.mp hg.1) i, ?_⟩
    have hsurj : Function.Surjective ((g i) ∘
        (Function.eval i : (∀ j, GrothendieckAddGroup (M j)) →
          GrothendieckAddGroup (M i))) :=
      (Function.surjective_eval (β := fun j ↦ GrothendieckAddGroup (N j)) i).comp hg.2
    exact hsurj.of_comp
  · intro hg
    exact Function.Bijective.piMap hg

end Pi

end Algebra.GrothendieckAddGroup
