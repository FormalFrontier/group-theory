/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Group diagrams as free products modulo arrow relations

For an arbitrary diagram `F : J ⥤ GrpCat`, `GrpCat.Colimits.ColimitType F` is the
free product of its object groups modulo the normal closure of the arrow relators.
The individual group laws are already imposed by Mathlib's `Monoid.CoprodI`.
The generator maps `ι` satisfy every diagram arrow. Compatible families into any
monoid, in an independent universe, descend uniquely by `desc` and `homEquiv`.

The raw carrier has universe `max u v` for object groups in `Type u` and objects
indexed by `J : Type v`; the morphism universe occurs only in a proposition.
The categorical cocone explicitly lifts every object to that adequate universe.
No preservation of arbitrary large colimits by `GrpCat.uliftFunctor` is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §6, describes
  group colimits by generators and arrow identifications.
* Mathlib's free products, formalized by David Wärn and Joachim Breitner, normal
  closure, formalized by Kexing Ying, and quotient groups, formalized by Kevin
  Buzzard and Patrick Massot, supply the constructions and universal properties.
  Mathlib's categorical colimit comparison supplies the leg-preserving isomorphism.
-/

@[expose] public section

universe u v h t

open CategoryTheory Limits

namespace GrpCat.Colimits

variable {J : Type v} [Category.{h} J] (F : J ⥤ GrpCat.{u})

local notation "ofF" => (Monoid.CoprodI.of (M := fun j => F.obj j))

/-- The arrow relators, oriented as target image times inverse source, in the
free product of the object groups. -/
def relators : Set (Monoid.CoprodI fun j => F.obj j) :=
  {r | ∃ (j k : J) (f : j ⟶ k) (a : F.obj j),
    r = ofF ((F.map f).hom a) * (ofF a)⁻¹}

/-- Membership in the set of arrow relators. -/
theorem mem_relators_iff (r : Monoid.CoprodI fun j => F.obj j) :
    r ∈ relators F ↔ ∃ (j k : J) (f : j ⟶ k) (a : F.obj j),
      r = ofF ((F.map f).hom a) * (ofF a)⁻¹ := Iff.rfl

/-- Each diagram arrow supplies a relator. -/
theorem arrow_relator_mem {j k : J} (f : j ⟶ k) (a : F.obj j) :
    ofF ((F.map f).hom a) * (ofF a)⁻¹ ∈ relators F :=
  ⟨j, k, f, a, rfl⟩

/-- The free product of the object groups modulo the normal closure of the
arrow-identification relators. -/
abbrev ColimitType : Type (max u v) :=
  Monoid.CoprodI (fun j => F.obj j) ⧸ Subgroup.normalClosure (relators F)

/-- The map of an object group into the arrow-relations quotient. -/
def ι (j : J) : F.obj j →* ColimitType F :=
  (QuotientGroup.mk' (Subgroup.normalClosure (relators F))).comp ofF

/-- The generator maps are the quotient projection on free-product generators.
This is not a simp rule: generator expressions are the normal form for descent. -/
theorem ι_apply (j : J) (a : F.obj j) :
    ι F j a = QuotientGroup.mk' (Subgroup.normalClosure (relators F))
      (ofF a) := rfl

/-- Every diagram arrow identifies its source generator with its target image. -/
@[simp]
theorem ι_map {j k : J} (f : j ⟶ k) (a : F.obj j) :
    ι F k ((F.map f).hom a) = ι F j a := by
  apply (QuotientGroup.eq_iff_div_mem
    (N := Subgroup.normalClosure (relators F))).mpr
  rw [div_eq_mul_inv]
  exact Subgroup.subset_normalClosure (arrow_relator_mem F f a)

/-- The generator maps form a compatible family. -/
@[simp]
theorem ι_comp_map {j k : J} (f : j ⟶ k) :
    (ι F k).comp (F.map f).hom = ι F j :=
  MonoidHom.ext (ι_map F f)

variable {H : Type t} [Monoid H]

/-- A compatible family annihilates the normal closure of the arrow relators.
The target needs only be a monoid: inverses are taken in the source groups. -/
theorem normalClosure_relators_le_ker (φ : ∀ j, F.obj j →* H)
    (hφ : ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j) :
    Subgroup.normalClosure (relators F) ≤ (Monoid.CoprodI.lift φ).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨j, k, f, a, rfl⟩
  change Monoid.CoprodI.lift φ (ofF ((F.map f).hom a) * (ofF a)⁻¹) = 1
  have ha : φ k ((F.map f).hom a) = φ j a := DFunLike.congr_fun (hφ f) a
  rw [← map_inv (ofF : F.obj j →* _) a, map_mul,
    Monoid.CoprodI.lift_of, Monoid.CoprodI.lift_of, ha,
    ← map_mul, mul_inv_cancel, map_one]

/-- Descend a compatible family of homomorphisms through the arrow-relations
quotient, using Mathlib's free-product lift and quotient-group lift. -/
def desc (φ : ∀ j, F.obj j →* H)
    (hφ : ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j) :
    ColimitType F →* H :=
  QuotientGroup.lift _ (Monoid.CoprodI.lift φ) (normalClosure_relators_le_ker F φ hφ)

/-- Descent on a quotient representative is the free-product lift. -/
@[simp]
theorem desc_mk (φ : ∀ j, F.obj j →* H)
    (hφ : ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j)
    (x : Monoid.CoprodI fun j => F.obj j) :
    desc F φ hφ (x : ColimitType F) = Monoid.CoprodI.lift φ x := rfl

/-- Descent agrees with the supplied family on each generator. -/
@[simp]
theorem desc_ι (φ : ∀ j, F.obj j →* H)
    (hφ : ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j)
    (j : J) (a : F.obj j) :
    desc F φ hφ (ι F j a) = φ j a :=
  Monoid.CoprodI.lift_of φ a

/-- Restricting descent to an object group recovers its supplied homomorphism. -/
@[simp]
theorem desc_comp_ι (φ : ∀ j, F.obj j →* H)
    (hφ : ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j) (j : J) :
    (desc F φ hφ).comp (ι F j) = φ j :=
  MonoidHom.ext (desc_ι F φ hφ j)

/-- Maps out of the arrow-relations quotient are determined by all object groups. -/
@[ext]
theorem hom_ext {f g : ColimitType F →* H}
    (hfg : ∀ j, f.comp (ι F j) = g.comp (ι F j)) : f = g := by
  apply QuotientGroup.monoidHom_ext
  apply Monoid.CoprodI.ext_hom
  exact hfg

/-- Descent from the restrictions of a homomorphism recovers that homomorphism. -/
@[simp]
theorem desc_restrict (f : ColimitType F →* H) :
    desc F (fun j => f.comp (ι F j))
      (fun {_ _} a => by rw [MonoidHom.comp_assoc, ι_comp_map]) = f := by
  apply hom_ext F
  intro j
  exact desc_comp_ι F _ _ j

/-- The universal property: maps into any independent-universe monoid are
exactly compatible families on the diagram. This is the free-product/normal-
relations construction of group colimits described by May, Chapter 2, §6. -/
def homEquiv : (ColimitType F →* H) ≃
    {φ : ∀ j, F.obj j →* H //
      ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j} where
  toFun f := ⟨fun j => f.comp (ι F j),
    fun {_ _} a => by rw [MonoidHom.comp_assoc, ι_comp_map]⟩
  invFun φ := desc F φ.val φ.property
  left_inv := desc_restrict F
  right_inv φ := Subtype.ext (funext (desc_comp_ι F φ.val φ.property))

/-- The forward universal equivalence restricts along the generator maps. -/
@[simp]
theorem homEquiv_apply (f : ColimitType F →* H) (j : J) :
    (homEquiv F f).val j = f.comp (ι F j) := rfl

/-- The inverse universal equivalence evaluates to the supplied family on generators. -/
@[simp]
theorem homEquiv_symm_apply_ι
    (φ : {φ : ∀ j, F.obj j →* H //
      ∀ {j k : J} (f : j ⟶ k), (φ k).comp (F.map f).hom = φ j})
    (j : J) (a : F.obj j) :
    (homEquiv F).symm φ (ι F j a) = φ.val j a :=
  desc_ι F φ.val φ.property j a

/-- The free-product lift of the generator family is the quotient projection. -/
@[simp]
theorem lift_ι : Monoid.CoprodI.lift (ι F) =
    QuotientGroup.mk' (Subgroup.normalClosure (relators F)) := by
  apply Monoid.CoprodI.ext_hom
  intro j
  exact Monoid.CoprodI.lift_comp_of (ι F) j

/-- The object-group images generate the quotient as a group. -/
@[simp]
theorem iSup_range_ι : (⨆ j, (ι F j).range) = ⊤ := by
  rw [← Monoid.CoprodI.range_eq_iSup, lift_ι, QuotientGroup.range_mk']

/-- The quotient cocone after explicitly lifting every object group into
`GrpCat.{max u v}`. Its legs transport `ι` along `MulEquiv.ulift`. -/
def cocone : Cocone (F ⋙ GrpCat.uliftFunctor.{v, u}) where
  pt := GrpCat.of (ColimitType F)
  ι :=
    { app := fun j => GrpCat.ofHom ((ι F j).comp MulEquiv.ulift.toMonoidHom)
      naturality := by
        intro j k f
        apply GrpCat.hom_ext
        exact MonoidHom.ext (fun a => ι_map F f a.down) }

/-- The lifted cocone leg on an element is its quotient generator. -/
@[simp]
theorem cocone_ι_app_apply (j : J) (a : ULift.{v} (F.obj j)) :
    GrpCat.Hom.hom (X := GrpCat.uliftFunctor.{v, u}.obj (F.obj j))
      (Y := (cocone F).pt) ((cocone F).ι.app j) a = ι F j a.down := rfl

/-- Transporting the legs of any lifted cocone along `MulEquiv.ulift.symm`
gives a compatible family on the original diagram. -/
theorem cocone_compatible (s : Cocone (F ⋙ GrpCat.uliftFunctor.{v, u}))
    {j k : J} (f : j ⟶ k) :
    ((s.ι.app k).hom.comp MulEquiv.ulift.symm.toMonoidHom).comp (F.map f).hom =
      (s.ι.app j).hom.comp MulEquiv.ulift.symm.toMonoidHom :=
  MonoidHom.ext fun a => ConcreteCategory.congr_hom (s.w f) (ULift.up a)

/-- The arrow-relations quotient is a colimit in the adequate carrier universe.
This constructs its universal property, rather than assuming preservation of a
large colimit by universe lift. -/
def coconeIsColimit : IsColimit (cocone F) where
  desc s := GrpCat.ofHom (desc F
    (fun j => (s.ι.app j).hom.comp MulEquiv.ulift.symm.toMonoidHom)
    (fun {_ _} f => cocone_compatible F s f))
  fac s j := by
    apply GrpCat.ext
    intro a
    exact desc_ι (H := s.pt) F
      (fun j => (s.ι.app j).hom.comp MulEquiv.ulift.symm.toMonoidHom)
      (fun {_ _} f => cocone_compatible F s f) j a.down
  uniq s m hm := by
    apply GrpCat.hom_ext
    apply hom_ext F
    intro j
    apply MonoidHom.ext
    intro a
    exact (ConcreteCategory.congr_hom (hm j) (ULift.up a)).trans
      (desc_ι (H := s.pt) F
        (fun j => (s.ι.app j).hom.comp MulEquiv.ulift.symm.toMonoidHom)
        (fun {_ _} f => cocone_compatible F s f) j a).symm

/-- The canonical comparison with any colimit of the same lifted diagram.
Both objects are in `GrpCat.{max u v}`. -/
def colimitIso (c : Cocone (F ⋙ GrpCat.uliftFunctor.{v, u})) (hc : IsColimit c) :
    GrpCat.of (ColimitType F) ≅ c.pt :=
  (coconeIsColimit F).coconePointUniqueUpToIso hc

/-- The canonical colimit comparison preserves every lifted leg. -/
@[simp, reassoc]
theorem cocone_ι_comp_colimitIso_hom
    (c : Cocone (F ⋙ GrpCat.uliftFunctor.{v, u})) (hc : IsColimit c) (j : J) :
    (cocone F).ι.app j ≫ (colimitIso F c hc).hom = c.ι.app j :=
  (coconeIsColimit F).comp_coconePointUniqueUpToIso_hom hc j

/-- The inverse canonical comparison preserves every lifted leg. -/
@[simp, reassoc]
theorem ι_comp_colimitIso_inv
    (c : Cocone (F ⋙ GrpCat.uliftFunctor.{v, u})) (hc : IsColimit c) (j : J) :
    c.ι.app j ≫ (colimitIso F c hc).inv = (cocone F).ι.app j :=
  (coconeIsColimit F).comp_coconePointUniqueUpToIso_inv hc j

end GrpCat.Colimits
