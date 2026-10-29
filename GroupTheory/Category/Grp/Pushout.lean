/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Group pushouts over a trivial vertex

For a homomorphism `f : A →* B`, the quotient of `B` by the normal closure of
`Set.range f` is the pushout of `f` and the homomorphism from `A` to any trivial
group `T`. The leg from `B` is the quotient projection and the leg from `T` is
the trivial homomorphism. The quotient and its universal map are Mathlib's
`QuotientGroup.mk'` and `QuotientGroup.lift`.

`QuotientGroup.liftNormalClosureRange` constructs the descended homomorphism.
`QuotientGroup.existsUnique_lift_normalClosure_range` gives the universal property
with independent source, quotient-source, trivial-vertex and target universes.
`GrpCat.isPushout_quotient_normalClosure` expresses the same square in `GrpCat`.
The remaining theorems identify the surjectivity and kernel of the leg from `B`
in any pushout of the same span. More generally, surjectivity of a span leg
is preserved by pushout along the other leg.

## References

* Mathlib's normal-closure API, formalized by Kexing Ying, and quotient-group
  universal property, formalized by Kevin Buzzard and Patrick Massot, supply
  the algebraic constructions.
* Mathlib's bundled groups, formalized by Johan Commelin, their epimorphism
  characterization, formalized by Jujian Zhang, and pushout squares,
  formalized by Kim Morrison, Joël Riou and Calle Sönne, supply the categorical
  universal property and comparison between pushouts on the ordinary quotient carrier.
-/

@[expose] public section

universe u v w z

namespace QuotientGroup

variable {A : Type u} {B : Type v} {T : Type w} {D : Type z}
variable [Monoid A] [Group B] [Monoid T] [Subsingleton T] [Monoid D]

/-- A homomorphism annihilating the image of `f` descends through its normal-closure
quotient, using `QuotientGroup.lift` on the same quotient carrier. -/
def liftNormalClosureRange (f : A →* B) (a : B →* D) (h : a.comp f = 1) :
    B ⧸ Subgroup.normalClosure (Set.range f) →* D :=
  lift _ a (Subgroup.normalClosure_le_normal (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun h x))

/-- The descended homomorphism agrees with the original map on representatives. -/
@[simp]
theorem liftNormalClosureRange_mk (f : A →* B) (a : B →* D)
    (h : a.comp f = 1) (x : B) :
    liftNormalClosureRange f a h (QuotientGroup.mk x) = a x := rfl

/-- Restriction along the quotient projection recovers the original homomorphism. -/
@[simp]
theorem liftNormalClosureRange_comp_mk' (f : A →* B) (a : B →* D)
    (h : a.comp f = 1) :
    (liftNormalClosureRange f a h).comp
      (mk' (Subgroup.normalClosure (Set.range f))) = a := rfl

/-- The restriction to `B` uniquely characterizes descent through the normal-closure
quotient. -/
theorem liftNormalClosureRange_unique (f : A →* B) (a : B →* D)
    (h : a.comp f = 1) {l : B ⧸ Subgroup.normalClosure (Set.range f) →* D}
    (hl : l.comp (mk' (Subgroup.normalClosure (Set.range f))) = a) :
    l = liftNormalClosureRange f a h :=
  monoidHom_ext _ (hl.trans (liftNormalClosureRange_comp_mk' f a h).symm)

/-- Compatible homomorphisms out of `B` and a trivial monoid `T` descend uniquely
through the quotient of `B` by the normal closure of the image of `f`.
The descended map is `QuotientGroup.lift`; its two restrictions
are the supplied maps, with no identification of `T` with a chosen singleton. -/
theorem existsUnique_lift_normalClosure_range (f : A →* B) (g : A →* T)
    (a : B →* D) (b : T →* D) (h : a.comp f = b.comp g) :
    ∃! l : B ⧸ Subgroup.normalClosure (Set.range f) →* D,
      l.comp (mk' (Subgroup.normalClosure (Set.range f))) = a ∧
        l.comp (1 : T →* B ⧸ Subgroup.normalClosure (Set.range f)) = b := by
  have ha : a.comp f = 1 := by
    have hb : b = 1 := Subsingleton.elim _ _
    simpa only [hb, MonoidHom.one_comp] using h
  refine ⟨liftNormalClosureRange f a ha,
    ⟨liftNormalClosureRange_comp_mk' f a ha, Subsingleton.elim _ _⟩, ?_⟩
  intro l hl
  exact liftNormalClosureRange_unique f a ha hl.1

end QuotientGroup

open CategoryTheory

namespace GrpCat

variable {A B T P : GrpCat.{u}}

/-- If a span leg is surjective, the opposite leg in any group pushout is
surjective. -/
theorem surjective_inl_of_isPushout_of_surjective {f : A ⟶ B} {g : A ⟶ T}
    {i : B ⟶ P} {j : T ⟶ P} (h : IsPushout f g i j)
    (hg : Function.Surjective g) : Function.Surjective i := by
  let : Epi g := (epi_iff_surjective g).2 hg
  let : Epi i := h.epi_inl_of_epi
  exact surjective_of_epi i

variable [Subsingleton T]

/-- The quotient by the normal closure of the image of `f` is the group pushout
of `f` and any map `g` to a trivial group. Both legs are the canonical maps:
the quotient projection from `B` and the trivial homomorphism from `T`. -/
theorem isPushout_quotient_normalClosure (f : A ⟶ B) (g : A ⟶ T) :
    IsPushout f g
      (ofHom (QuotientGroup.mk' (Subgroup.normalClosure (Set.range f.hom))))
      (ofHom (1 : T →* B ⧸ Subgroup.normalClosure (Set.range f.hom))) := by
  apply IsPushout.mk'
  · apply hom_ext
    change (QuotientGroup.mk' _).comp f.hom = (1 : T →* _).comp g.hom
    rw [MonoidHom.one_comp]
    apply MonoidHom.ext
    intro x
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  · intro D φ ψ h _
    apply hom_ext
    exact QuotientGroup.monoidHom_ext _ (congrArg Hom.hom h)
  · intro D a b h
    obtain ⟨l, hl, _⟩ := QuotientGroup.existsUnique_lift_normalClosure_range
      f.hom g.hom a.hom b.hom (congrArg Hom.hom h)
    exact ⟨ofHom l, hom_ext hl.1, hom_ext hl.2⟩

/-- In any group pushout with a trivial second vertex, the leg from `B` is
surjective. -/
theorem surjective_inl_of_isPushout {f : A ⟶ B} {g : A ⟶ T}
    {i : B ⟶ P} {j : T ⟶ P} (h : IsPushout f g i j) : Function.Surjective i := by
  apply surjective_inl_of_isPushout_of_surjective h
  intro t
  exact ⟨1, Subsingleton.elim _ _⟩

/-- In any group pushout with a trivial second vertex, the kernel of the leg
from `B` is exactly the normal closure of the image of `f`. -/
theorem ker_inl_of_isPushout {f : A ⟶ B} {g : A ⟶ T}
    {i : B ⟶ P} {j : T ⟶ P} (h : IsPushout f g i j) :
    i.hom.ker = Subgroup.normalClosure (Set.range f.hom) := by
  let hq := isPushout_quotient_normalClosure f g
  let e := hq.isoIsPushout B T h
  have he : e.hom.hom.comp
      (QuotientGroup.mk' (Subgroup.normalClosure (Set.range f.hom))) = i.hom :=
    congrArg Hom.hom (IsPushout.inl_isoIsPushout_hom B T hq h)
  rw [← he, MonoidHom.ker_comp_of_injective _ _ e.groupIsoToMulEquiv.injective,
    QuotientGroup.ker_mk']

end GrpCat
