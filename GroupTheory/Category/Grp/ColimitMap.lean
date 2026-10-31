/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import GroupTheory.Category.Grp.Colimits

/-!
# Maps between group-diagram colimits

A family of homomorphisms commuting with the arrows of two group diagrams induces
`GrpCat.Colimits.map` between their canonical colimits. The object groups of the
two diagrams may lie in independent universes. The induced map is characterized
by its restrictions to the object groups, and respects identities and composition.
-/

@[expose] public section

universe uJ vJ uF uG uK

open CategoryTheory

namespace GrpCat.Colimits

variable {J : Type uJ} [Category.{vJ} J]
  {F : J ⥤ GrpCat.{uF}} {G : J ⥤ GrpCat.{uG}} {K : J ⥤ GrpCat.{uK}}

/-- The homomorphism between the canonical colimits induced by a family commuting
with every diagram arrow. The source and target group universes are independent. -/
def map (α : ∀ j, F.obj j →* G.obj j)
    (hα : ∀ {j k : J} (f : j ⟶ k),
      (α k).comp (F.map f).hom = (G.map f).hom.comp (α j)) :
    ColimitType F →* ColimitType G :=
  desc F (fun j => (ι G j).comp (α j)) (fun {_ _} f => by
    rw [MonoidHom.comp_assoc, hα f, ← MonoidHom.comp_assoc, ι_comp_map])

variable (α : ∀ j, F.obj j →* G.obj j)
  (hα : ∀ {j k : J} (f : j ⟶ k),
    (α k).comp (F.map f).hom = (G.map f).hom.comp (α j))

/-- The induced map sends an object-group generator to its component image. -/
@[simp]
theorem map_ι (j : J) (a : F.obj j) :
    map α hα (ι F j a) = ι G j (α j a) :=
  desc_ι F (fun j => (ι G j).comp (α j)) _ j a

/-- Restricting the induced map to an object group gives its component followed
by the target generator map. -/
@[simp]
theorem map_comp_ι (j : J) :
    (map α hα).comp (ι F j) = (ι G j).comp (α j) :=
  MonoidHom.ext (map_ι α hα j)

/-- A homomorphism between the canonical colimits is the induced map precisely
when it has the prescribed restrictions to every object group. -/
theorem eq_map_iff (f : ColimitType F →* ColimitType G) :
    f = map α hα ↔ ∀ j, f.comp (ι F j) = (ι G j).comp (α j) := by
  constructor
  · rintro rfl
    exact map_comp_ι α hα
  · intro hf
    apply hom_ext F
    intro j
    exact (hf j).trans (map_comp_ι α hα j).symm

/-- Identity components induce the identity on the canonical colimit. -/
@[simp]
theorem map_id :
    map (fun j => MonoidHom.id (F.obj j)) (fun {_ _} _ => rfl) =
      MonoidHom.id (ColimitType F) := by
  apply hom_ext F
  intro j
  exact map_comp_ι _ _ j

/-- Composition of component families induces composition on canonical colimits. -/
@[simp]
theorem map_comp (β : ∀ j, G.obj j →* K.obj j)
    (hβ : ∀ {j k : J} (f : j ⟶ k),
      (β k).comp (G.map f).hom = (K.map f).hom.comp (β j)) :
    map (fun j => (β j).comp (α j))
      (fun {_ _} f => by
        rw [MonoidHom.comp_assoc, hα f, ← MonoidHom.comp_assoc, hβ f,
          MonoidHom.comp_assoc]) =
      (map β hβ).comp (map α hα) := by
  apply hom_ext F
  intro j
  apply MonoidHom.ext
  intro a
  simp only [MonoidHom.comp_apply, map_ι]

end GrpCat.Colimits

namespace GrpCat.Colimits

variable {J : Type uJ} [Category.{vJ} J]

/-- For a natural transformation of diagrams in a common group universe, the raw
induced homomorphism is the categorical map between the already constructed
lifted colimit cocones. Compatibility is supplied by naturality; no preservation
of arbitrary colimits by universe lift is assumed. -/
theorem map_eq_isColimit_map {F' G' : J ⥤ GrpCat.{uF}} (δ : F' ⟶ G') :
    GrpCat.ofHom (map (fun j => (δ.app j).hom)
      (fun {_ _} f => by
        simpa only [GrpCat.hom_comp] using
          congrArg GrpCat.Hom.hom (δ.naturality f))) =
      (coconeIsColimit F').map (cocone G')
        (CategoryTheory.Functor.whiskerRight δ GrpCat.uliftFunctor.{uJ, uF}) := by
  rfl

end GrpCat.Colimits
