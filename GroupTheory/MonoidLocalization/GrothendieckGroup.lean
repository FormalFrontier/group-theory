/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Additive and bilinear Grothendieck lifts

The universal property of the Grothendieck additive group is additive in the supplied
homomorphism. `Algebra.GrothendieckAddGroup.liftAddEquiv` equips Mathlib's equivalence
`Algebra.GrothendieckAddGroup.lift` with this structure, retaining both its forward map and
its inverse, restriction along `Algebra.GrothendieckAddGroup.of`.

`Algebra.GrothendieckAddGroup.lift_injective_iff` characterizes injectivity of a lift by
reflection of stable equality in the source monoid.
`Algebra.GrothendieckAddGroup.lift_of_comp_injective_iff` specializes this criterion to the
homomorphism induced by an additive homomorphism between commutative monoids.

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

end Algebra.GrothendieckAddGroup
